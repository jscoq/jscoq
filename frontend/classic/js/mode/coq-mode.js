// CodeMirror, copyright (c) by Marijn Haverbeke and others
// Distributed under an MIT license: http://codemirror.net/LICENSE

// Coq mode created by Valentin Robert, Benoît Pin, Emilio J. Gallego
// Arias, and others

/************************************************************************/
/*  v      *      CodeMirror Mode for the Coq Proof Assistant           */
/* <O___,, *         Specialized to jsCoq - Copyright 2016              */
/*   \VV/  **************************************************************/
/*    //   *      This file is distributed under the terms of the       */
/*         *                      MIT license                           */
/************************************************************************/

/************************************************************************/
/* General information: the mode provides only a tokenizer, completion  */
/* and other advanced CM features are TODO.                             */
/*                                                                      */
/* New tokens declared:                                                 */
/*                                                                      */
/* - statementend: Dot ending a Coq statement has been detected         */
/* - tactic: Coq tactic                                                 */
/*                                                                      */
/* BUGS:                                                                */
/*                                                                      */
/*   MUST be fixed before submitting upstream.                          */
/*                                                                      */
/* - Braces handling doesn't always work. Example: brace starting a     */
/*   line.                                                              */
/*                                                                      */
/*   I suggest we use the regular expressions used by CoqIDE/emacs      */
/*   thus a small rewrite is needed.                                    */
/*                                                                      */
/* TODO:                                                                */
/*                                                                      */
/* - Rebase before submission                                           */
/* - comment addon                                                      */
/* - indent                                                             */
/* - completion                                                         */
/*                                                                      */
/************************************************************************/

import CodeMirror from 'codemirror';

(function(mod) {
  if (typeof exports == "object" && typeof module == "object") // CommonJS
    mod(require("codemirror"));
  else if (typeof define == "function" && define.amd) // AMD
    define(["codemirror"], mod);
  else // Plain browser env
    mod(CodeMirror);
})(function(CodeMirror) {
  "use strict";

  CodeMirror.defineMode('coq', function(_config, _parserConfig) {

    var vernacular = [
      'Abort', 'About', 'Add', 'All', 'Arguments', 'Asymmetric', 'Axiom',
      'Bind',
      'Canonical', 'Check', 'Class', 'Close', 'Coercion', 'CoFixpoint', 'Comments',
      'CoInductive', 'Compute', 'Context', 'Constructors', 'Contextual', 'Corollary',
      'Defined', 'Definition', 'Delimit',
      'Fail',
      'Eval',
      'End', 'Example', 'Export',
      'Fact', 'Fixpoint', 'From',
      'Global', 'Goal', 'Graph',
      'Hint', 'Hypotheses', 'Hypothesis',
      'Implicit', 'Implicits', 'Import', 'Inductive', 'Infix', 'Instance',
      'Lemma', 'Let', 'Local', 'Ltac',
      'Module', 'Morphism',
      'Next', 'Notation',
      'Obligation', 'Open',
      'Parameter', 'Parameters', 'Prenex', 'Print', 'Printing', 'Program',
      'Patterns', 'Projections', 'Proof',
      'Proposition',
      'Qed',
      'Record', 'Relation', 'Remark', 'Require', 'Reserved', 'Resolve', 'Rewrite',
      'Save', 'Scope', 'Search', 'SearchAbout', 'Section', 'Set', 'Show', 'Strict', 'Structure',
      'Tactic', 'Time', 'Theorem', 'Types',
      'Unset',
      'Variable', 'Variables', 'View'
    ];

    var gallina = [
      'as',
      'at',
      'cofix', 'crush',
      'else', 'end',
      'False', 'fix', 'for', 'forall', 'fun',
      'if', 'in', 'is',
      'let',
      'match',
      'of',
      'Prop',
      'return',
      'struct',
      'then', 'True', 'Type',
      'when', 'with'
    ];

    var tactics = [
      'after', 'apply', 'assert', 'auto', 'autorewrite',
      'case', 'change', 'clear', 'compute', 'congruence', 'constructor',
      'congr', 'cut', 'cutrewrite',
      'dependent', 'destruct',
      'eapply', 'eauto', 'ecase', 'econstructor', 'edestruct',
      'ediscriminate', 'eelim', 'eenough', 'eexists', 'eexact', 'einduction',
      'einjection', 'eleft', 'epose', 'eright', 'esplit',
      'elim', 'enough', 'exists',
      'field', 'firstorder', 'fold', 'fourier',
      'generalize',
      'have', 'hnf',
      'induction', 'injection', 'instantiate', 'intro', 'intros', 'inversion',
      'left',
      'move',
      'pattern', 'pose',
      'refine', 'remember', 'rename', 'repeat', 'replace', 'revert', 'rewrite',
      'right', 'ring',
      'set', 'simpl', 'specialize', 'split', 'subst', 'suff', 'symmetry',
      'transitivity', 'trivial', 'try',
      'unfold', 'unlock', 'using',
      'vm_compute',
      'where', 'wlog'
    ];

    var terminators = [
      'assumption',
      'eassumption',
      'by',
      'contradiction',
      'discriminate',
      'easy',
      'exact',
      'now',
      'lia',
      'omega',
      'reflexivity',
      'tauto'
    ];

    var admitters = [
      'admit',
      'Admitted'
    ];

    const lex_operators =   /* multi-character operators */
      /=+>|:=|<:|<<:|:>|-+>|[<>]-+>?|\\\/|\/\\|>=|<=+|<>|\+\+|::|\|\||&&|\.\./;
      
    const lex_brackets = /\.\(|\{\||\|\}|`\{|`\(/;

    // Map assigning each keyword a category.
    var words = {};

    // We map
    // - gallina keywords -> CM keywords
    // - vernaculars      -> CM builtins
    // - admitters        -> CM keywords XXX
    gallina    .map(function(word){words[word] = 'keyword';});
    admitters  .map(function(word){words[word] = 'keyword';});
    vernacular .map(function(word){words[word] = 'builtin';});

    tactics    .map(function(word){words[word] = 'tactic';});
    terminators.map(function(word){words[word] = 'terminator';});

    /*
      Coq mode defines the following state variables:

      - begin_sentence: only \s caracters seen from the last sentence.

      - is_head: at first (non-comment, non-space) token of sentence.

      - sentence_kind: kind of the head token.

      - commentLevel [:int] = Level of nested comments.

      - tokenize [:func] = current active tokenizer. We provide 4 main ones:

        + tokenBase: Main parser, it reads the next character and
          setups the next tokenizer. In particular it takes care of
          braces. It doesn't properly analyze the sentences and
          bracketing.

        + tokenStatementEnd: Called when a dot is found in tokenBase,
          it looks ahead on the string and returns statement end.

        + tokenString: Takes care of escaping.

        + tokenComment: Takes care of nested comments.

     */

    /*
      Codemirror lexing functions:

      - eat(s) = eat next char if s
      - eatWhile(s) = eat s until fails
      - match(regexp) => return array of matches and optionally eat

     */
    function tokenBase(stream, state) {

      var at_sentence_start = state.begin_sentence;

      state.is_head = false;

      // If any space in the input, return null.
      if(stream.eatSpace())
        return null;

      if (stream.match(lex_operators)) {
        state.begin_sentence = false;
        return 'operator';
      }

      //if (stream.match(lex_brackets))  return 'bracket';
      // ^ skipped, for the time being, because matchbracket does not support
      //   multi-character brackets.

      if (at_sentence_start) {
        if (stream.match(/[-*+]+|[{}]/)) return 'coq-bullet';
        if (stream.match(/\d+\s*:/)) return 'coq-focus';
      }

      var ch = stream.next();

      // Preserve begin sentence after comment.
      if (ch === '(') {
        if (stream.peek() === '*') {
          stream.next();
          state.commentLevel++;
          state.tokenize = tokenComment;
          return state.tokenize(stream, state);
        }
        state.begin_sentence = false;
        return 'parenthesis';
      }

      if( ! (/\s/.test(ch)) ) {
        state.begin_sentence = false;
      }

      if(ch === '.') {
        state.tokenize = tokenStatementEnd;
        return state.tokenize(stream, state);
      }

      if (ch === '"') {
        state.tokenize = tokenString;
        return state.tokenize(stream, state);
      }

      if(ch === ')')
        return 'parenthesis';

      if (/\d/.test(ch)) {
        stream.eatWhile(/[\d]/);
        /*
        if (stream.eat('.')) {
          stream.eatWhile(/[\d]/);
        }
        */
        return 'number';
      }

      if ( /[+\-*&%=<>!?|,;:\^#@~`]/.test(ch)) {
        return 'operator';
      }

      if(/[\[\]]/.test(ch)) {
        return 'bracket';
      }

      /* Identifier or keyword*/
      if (/\w/.test(ch))
        stream.eatWhile(/[\w']/);

      var cur = stream.current(),
          kind = Object.hasOwn(words, cur) ? words[cur] : 'variable';

      if (at_sentence_start) {
        state.sentence_kind = kind;
        state.is_head = true;
      }
      else if (kind === 'tactic' && state.sentence_kind === 'builtin') {
        /* tactics should not occur in vernac (unless "ltac:" is used?) */
        kind = 'variable';
      }

      return kind;
    }

    function tokenString(stream, state) {
      var next, end = false, escaped = false;
      while ((next = stream.next()) != null) {
        if (next === '"' && !escaped) {
          end = true;
          break;
        }
        escaped = !escaped && next === '\\';
      }
      if (end && !escaped) {
        state.tokenize = tokenBase;
      }
      return 'string';
    }

    function tokenComment(stream, state) {
      var ch;
      while(state.commentLevel && (ch = stream.next())) {
        if(ch === '(' && stream.peek() === '*') {
          stream.next();
          state.commentLevel++;
        }

        if(ch === '*' && stream.peek() === ')') {
          stream.next();
          state.commentLevel--;
        }
      }

      if(!state.commentLevel)
        state.tokenize = tokenBase;

      return 'comment';
    }

    function tokenStatementEnd(stream, state) {
      state.tokenize = tokenBase;

      if(stream.eol() || stream.match(/\s/, false)) {
        state.begin_sentence = true;
        state.sentence_kind = undefined;
        return 'statementend';
      }
    }

    return {
      startState: function() {
        return {begin_sentence: true, is_head: false, tokenize: tokenBase, commentLevel: 0};
      },

      token: function(stream, state) {
        return state.tokenize(stream, state);
      },

      blockCommentStart: "(*",
      blockCommentEnd  : "*)",
      lineComment: null
    };
  });

  CodeMirror.defineMIME('text/x-coq', {
    name: 'coq'
  });

});

// Local Variables:
// js-indent-level: 2
// End:
