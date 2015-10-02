// dependencies:
//   defineMathMode(): addon/mode/multiplex.js, optionally addon/mode/stex/stex.js
//   hookMath(): MathJax

"use strict";

// Wrap mode to skip formulas (e.g. $x*y$ shouldn't start italics in markdown).
// TODO: doesn't handle escaping, e.g. \$.  Doesn't check spaces before/after $ like pandoc.
// TODO: this might not exactly match the same things as formulaRE in processLine().

// We can't just construct a mode object, because there would be no
// way to use; we have to register a constructor, with a name.
CodeMirror.defineMathMode = function(name, outerModeSpec) {
  CodeMirror.defineMode(name, function(cmConfig) {
    var outerMode = CodeMirror.getMode(cmConfig, outerModeSpec);
    var innerMode = CodeMirror.getMode(cmConfig, "text/x-stex");
    return CodeMirror.multiplexingMode(
      outerMode,
      // "keyword" is how stex styles math delimiters.
      // "delim" tells us not to pick up this style as math style.
      {open: "$$", close: "$$", mode: innerMode, delimStyle: "keyword delim"},
      {open:  "$", close: "$",  mode: innerMode, delimStyle: "keyword delim"},
      {open: "\\(", close: "\\)", mode: innerMode, delimStyle: "keyword delim"},
      {open: "\\[", close: "\\]", mode: innerMode, delimStyle: "keyword delim"});
  });
};

// Usage: first call CodeMirror.hookMath(editor, MathJax), then editor.renderAllMath() to process initial content.
// TODO: simplify usage when initial pass becomes cheap.
// TODO: use defineOption(), support clearing widgets and removing handlers.
CodeMirror.hookMath = function(editor, MathJax) {
  // Logging
  // -------
  var timestampMs = ((window.performance && window.performance.now) ?
                     function() { return window.performance.now(); } :
                     function() { return new Date().getTime(); });
  function formatDuration(ms) { return (ms / 1000).toFixed(3) + "s"; }

  var t0 = timestampMs();

  // Goal: Prevent errors on IE (but do strive to log somehow if IE Dev Tools are open).
  // While we are at it, prepend timestamp to all messages.

  // The only way to keep console messages associated with original
  // line is to use original `console.log` or its .bind().
  // The way to use these helpers is the awkward:
  //
  //     logf()(message, obl)
  //     errorf()(message, obl)
  //
  function logmaker(logMethod) {
    try {
      // console.log is native function, has no .bind in some browsers.
      return Function.prototype.bind.call(console[logMethod], console,
                                          formatDuration(timestampMs() - t0));
    } catch(err) {
      return function(var_args) {
        try {
          var args = Array.prototype.slice.call(arguments, 0);
          args.unshift(formatDuration(timestampMs() - t0));
          if(console[logMethod].apply) {
            console[logMethod].apply(console, args);
          } else {
            /* IE's console.log doesn't have .apply, .call, or bind. */
            console.log(Array.prototype.slice.call(args));
          }
        } catch(err) {}
      };
    }
  }
  function logf() { return logmaker("log"); }
  function errorf() { return logmaker("error"); }

  // Log time if non-negligible.
  function logFuncTime(func) {
    return function(var_args) {
      var start = timestampMs();
      func.apply(this, arguments);
      var duration = timestampMs() - start;
      if(duration > 100) {
        logf()((func.name || "<???>") + "() took " + formatDuration(duration));
      }
    };
  }

  function catchAllErrors(func) {
    return function(var_args) {
      try {
        return func.apply(this, arguments);
      } catch(err) {
        errorf()("catching error:", err);
      }
    }
  }

  // Position arithmetic
  // -------------------

  var Pos = CodeMirror.Pos;

  // Return negative / 0 / positive.  a < b iff posCmp(a, b) < 0 etc.
  function posCmp(a, b) {
    return (a.line - b.line) || (a.ch - b.ch);
  }

  // True if inside, false if on edge.
  function posInsideRange(pos, fromTo) {
    return posCmp(fromTo.from, pos) < 0 && posCmp(pos, fromTo.to) < 0;
  }

  // True if there is at least one character in common, false if just touching.
  function rangesOverlap(fromTo1, fromTo2) {
    return (posCmp(fromTo1.from, fromTo2.to) < 0 &&
            posCmp(fromTo2.from, fromTo1.to) < 0);
  }

  // Track currently-edited formula
  // ------------------------------
  // TODO: refactor this to generic simulation of cursor leave events.

  var doc = editor.getDoc();

  // If cursor is inside a formula, we don't render it until the
  // cursor leaves it.  To cleanly detect when that happens we
  // still markText() it but without replacedWith and store the
  // marker here.
  var unrenderedMath = null;

  function unrenderRange(fromTo) {
    if(unrenderedMath !== null) {
      var oldRange = unrenderedMath.find();
      if(oldRange !== undefined) {
        var text = doc.getRange(oldRange.from, oldRange.to);
        errorf()("overriding previous unrenderedMath:", text);
      } else {
        errorf()("overriding unrenderedMath whose .find() === undefined", text);
      }
    }
    logf()("unrendering math", doc.getRange(fromTo.from, fromTo.to));
    unrenderedMath = doc.markText(fromTo.from, fromTo.to);
    unrenderedMath.xMathState = "unrendered"; // helps later remove only our marks.
  }

  function unrenderMark(mark) {
    var range = mark.find();
    if(range === undefined) {
      errorf()(mark, "mark.find() === undefined");
    } else {
      unrenderRange(range);
    }
    mark.clear();
  }

  editor.on("cursorActivity", catchAllErrors(function(doc) {
    if(unrenderedMath !== null) {
      // TODO: selection behavior?
      // TODO: handle multiple cursors/selections
      var cursor = doc.getCursor();
      var unrenderedRange = unrenderedMath.find();
      if(unrenderedRange === undefined) {
        // This happens, not yet sure when and if it's fine.
        errorf()(unrenderedMath, ".find() === undefined");
        return;
      }
      if(posInsideRange(cursor, unrenderedRange)) {
        logf()("cursorActivity", cursor, "in unrenderedRange", unrenderedRange);
      } else {
        logf()("cursorActivity", cursor, "left unrenderedRange.", unrenderedRange);
        unrenderedMath = null;
        processMath(unrenderedRange.from, unrenderedRange.to);
        flushMarkTextQueue();
      }
    }
  }));

  // Rendering on changes
  // --------------------

  function createMathElement(from, to) {
    // TODO: would MathJax.HTML make this more portable?
    var text = doc.getRange(from, to);
    var elem = document.createElement("span");
    // Display math becomes a <div> (inside this <span>), which
    // confuses CM badly ("DOM node must be an inline element").
    elem.style.display = "inline-block";
    if(/\\(?:re)?newcommand/.test(text)) {
      // \newcommand{...} would render empty, which makes it hard to enter it for editing.
      text = text + " \\(" + text + "\\)";
    }
    elem.appendChild(document.createTextNode(text));
    elem.title = text;

    var isDisplay = /^\$\$|^\\\[|^\\begin/.test(text);  // TODO: probably imprecise.

    // TODO: style won't be stable given surrounding edits.
    // This appears to work somewhat well but only because we're
    // re-rendering too aggressively (e.g. one line below change)...

    // Sample style one char into the formula, because it's null at
    // start of line.
    var insideFormula = Pos(from.line, from.ch + 1);
    var tokenType = editor.getTokenAt(insideFormula, true).type;
    var className = isDisplay ? "display_math" : "inline_math";
    if(tokenType && !/delim/.test(tokenType)) {
      className += " cm-" + tokenType.replace(/ +/g, " cm-");
    }
    elem.className = className;
    return elem;
  }

  // MathJax returns rendered DOMs asynchroonously.
  // Batch inserting those into the editor to reduce layout & painting.
  var markTextQueue = [];
  var flushMarkTextQueue = logFuncTime(function flushMarkTextQueue() {
    editor.operation(function() {
      for(var i = 0; i < markTextQueue.length; i++) {
        markTextQueue[i]();
      }
      markTextQueue = [];
    });
  });

  function processMath(from, to) {
    var elem = createMathElement(from, to);
    var text = elem.innerHTML;
    logf()("typesetting", text, elem);
    MathJax.Hub.Queue(["Typeset", MathJax.Hub, elem]);
    MathJax.Hub.Queue(function() {
      logf()("done typesetting", text);
      // TODO: what if doc changed while MathJax was typesetting?
      // TODO: behavior during selection?
      var cursor = doc.getCursor();

      if(posInsideRange(cursor, {from: from, to: to})) {
        // This doesn't normally happen during editing, more likely
        // during initial pass.
        errorf()("posInsideRange", cursor, from, to, "=> not rendering");
        unrenderRange({from: from, to: to});
      } else {
        markTextQueue.push(function() {
          var mark = doc.markText(from, to, {replacedWith: elem,
                                             clearOnEnter: false});
          mark.xMathState = "rendered"; // helps later remove only our marks.
          CodeMirror.on(mark, "beforeCursorEnter", catchAllErrors(function() {
            unrenderMark(mark);
          }));
        });
      }
    });
  }

  // TODO: multi line \[...\]. Needs an approach similar to overlay modes.
  function processLine(lineHandle) {
    var text = lineHandle.text;
    var line = doc.getLineNumber(lineHandle);
    //logf()("processLine", line, text);

    // TODO: At least unit test this regexp mess.

    // TODO: doesn't handle escaping, e.g. \$.  Doesn't check spaces before/after $ like pandoc.
    // TODO: matches inner $..$ in $$..$ etc.
    // JS has lookahead but not lookbehind.
    // For \newcommand{...} can't match end reliably, just consume till last } on line.
    var formulaRE = /\$\$.*?[^$\\]\$\$|\$.*?[^$\\]\$|\\\(.*?[^$\\]\\\)|\\\[.*?[^$\\]\\\]|\\begin\{([*\w]+)\}.*?\\end{\1}|\\(?:eq)?ref{.*?}|\\(?:re)?newcommand\{.*\}/g;
    var match;
    while((match = formulaRE.exec(text)) != null) {
      var fromCh = match.index;
      var toCh = fromCh + match[0].length;
      processMath(Pos(line, fromCh), Pos(line, toCh));
    }
  }

  function clearOurMarksInRange(from, to) {
    // doc.findMarks() added in CM 3.22.
    var oldMarks = doc.findMarks ? doc.findMarks(from, to) : doc.getAllMarks();
    for(var i = 0; i < oldMarks.length; i++) {
      var mark = oldMarks[i];
      if(mark.xMathState === undefined) {
        logf()("not touching foreign mark at", mark.find());
        continue;
      }

      // Verify it's in range, even after findMarks() - it returns
      // marks that touch the range, we want at least one char overlap.
      var found = mark.find();
      if(found.line !== undefined ?
         /* bookmark */ posInsideRange(found, {from: from, to: to}) :
         /* marked range */ rangesOverlap(found, {from: from, to: to}))
      {
        logf()("cleared mark at", found, "as part of range:", from, to);
        mark.clear();
      }
    }
  }

  // CM < 4 batched editor's "change" events via a .next property, which we'd
  // have to chase - and what's worse, adjust all coordinates.
  // Documents' "change" events were never batched, so not a problem.
  CodeMirror.on(doc, "change", catchAllErrors(logFuncTime(function processChange(doc, changeObj) {
    logf()("change", changeObj);
    // changeObj.{from,to} are pre-change coordinates; adding text.length
    // (number of inserted lines) is a conservative(?) fix.
    // TODO: use cm.changeEnd()
    var endLine = changeObj.to.line + changeObj.text.length + 1;
    clearOurMarksInRange(Pos(changeObj.from.line, 0), Pos(endLine, 0));
    doc.eachLine(changeObj.from.line, endLine, processLine);
    if("next" in changeObj) {
      errorf()("next");
      processChange(changeObj.next);
    }
    MathJax.Hub.Queue(flushMarkTextQueue);
  })));

  // First pass - process whole document.
  editor.renderAllMath = logFuncTime(function renderAllMath() {
    doc.eachLine(processLine);
    MathJax.Hub.Queue(flushMarkTextQueue);
    MathJax.Hub.Queue(function() { logf()("-- All math rendered. --"); });
  })

  // Make sure stuff doesn't somehow remain in markTextQueue.
  setInterval(function() {
    if(markTextQueue.length !== 0) {
      errorf()("Fallaback flushMarkTextQueue:", markTextQueue.length, "elements");
      flushMarkTextQueue();
    }
  }, 500);
}
