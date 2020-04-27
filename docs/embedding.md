# Embedding jsCoq

This quick tutorial will allow you to embed jsCoq in your web page.
It is especially useful when you have generated your page using
`coqdoc`.

## Preparation

The easiest way to obtain a distribution of jsCoq for the purpose of serving as part of your site is via `npm`.
If you already have a `package.json` file in your project, great.
Otherwise, in the root directory of your project, run `npm init`.
You will be asked to type the name of the project and a few other details, and then a `package.json` will be created.
Of course, creating a `package.json` file with any text editor is also acceptable.

Now run:
```
% npm i jscoq
```

And you have installed jsCoq in your project!
You will find it under `node_modules/jscoq`.
To test your new setup, serve your project root directory over HTTP(S), and navigate to `node_modules/jscoq/index.html`.

![screenshot](npm-landing-screenshot.png)

## Combining with your Coq development

If you're starting fresh, copying `node_modules/examples/npm-template.html` into the root directory of your project and writing your content there would be easiest.

Notice that if you want to put your HTML file(s) in a subfolder, you will have to adjust the paths (`<script src="...">`, `base_path: '...'`, and `'./node_modules'`) to the appropriate relative or absolute URL paths.

Sometimes, though, you will already have an HTML document, and want to "inject" jsCoq into it.
This is typical when using `coqdoc`:
your development is contained in a `.v` file, which `coqdoc` transforms into HTML.

The following boilerplate code can help you get started.

```js
/**
 * Injects jsCoq into an existing page.
 * This script has to be at the end of the body so that it runs after
 * the page DOM has loaded.
 */

function jsCoqInject() {
    document.body.classList.add('toggled');
    document.body.id = 'ide-wrapper';
}

var jsCoqShow = (localStorage.jsCoqShow !== 'false');

var jscoq_ids  = ['#main > div.code'];
var jscoq_opts = {
    show:      jsCoqShow,
    focus:     false,
    replace:   true,
    base_path: './node_modules/jscoq/',
    editor:    { mode: { 'company-coq': true }, keyMap: 'default' },
    all_pkgs:  ['init',
                'coq-base', 'coq-collections', 'coq-arith', 'coq-reals'],
    init_pkgs: ['init'],
    init_import: ['utf8'],
    implicit_libs: true
};

function jsCoqLoad() {
    // - remove empty code fragments (coqdoc generates some spurious ones)
    for (let sel of jscoq_ids) {
        for (let el of document.querySelectorAll(sel)) {
            if (el.textContent.match(/^\s*$/)) {
                el.parentElement.insertBefore(document.createElement('p'), el);
                el.remove();
            }
        }
    }

    JsCoq.start(jscoq_opts.base_path, './node_modules', jscoq_ids, jscoq_opts)
        .then(coq => {
            window.coq = coq;
            window.addEventListener('beforeunload', () => { localStorage.jsCoqShow = coq.layout.isVisible(); });
            document.querySelector('#page').focus();
        });

    if (jscoq_opts.show)
        document.body.classList.add('jscoq-launched');
}

if (location.search === '') {
    jsCoqInject();
    jsCoqLoad();
}
```

Copy it to <i>e.g.</i> `jscoq-embed.js` in your project, and then add the following two `<script>` tags at the end of your `<body>`:

```html
<script src="node_modules/jscoq/jscoq-loader.js"></script>
<script src="jscoq-embed.js"></script>
```

If you want to add those lines automatically as part as your build process, you can use [this nifty `gawk` script](./inject-jscoq.gawk).

## Instrumenting CoqDoc to generate HTML

An alternative to instrument CoqDoc vanilla HTML code is to use `udoc`.

`udoc` is a `coqdoc` replacement that is better suited to produce
jsCoq output while (mostly) remaining compatible is being developed at
https://github.com/ejgallego/udoc

It works OK for converting `coqdoc` files, but it may produce some
artifacts and have bugs; feel free to submit improvements.

## Main entry point from HTML and API

jsCoq's main entry point is the `CoqManager` JavaScript object used for
launching a Coq worker and embedding Coq functionality in
your particular application, blog, or webpage. The basic pattern to
add jsCoq to webpage with Coq code is:

```javascript
  <script src="$path/ui-js/jscoq-loader.js" type="text/javascript"></script>
  <script type="text/javascript">
    loadJsCoq($path).then( () => new CoqManager ($list_of_ids, {$options}) );
  </script>
```

where `$path` is the path the jsCoq distribution, and `$list_of_ids` is
a list of `<textarea>`s or `<div>`s that will form the Coq document.
CSS selectors are also allowed as part of `$list_of_ids`: all matching elements
will be added to the document.
See below for available `$options`.

The jsCoq [landing webpage](index.html) is a good running example.

### Options

jsCoq accepts the following options as an optional second parameter to
the `CoqManager` constructor:

| Key             | Type            | Default         | Description                                                                                                   |
|-----------------|-----------------|-----------------|---------------------------------------------------------------------------------------------------------------|
| `base_path`     | string          | `'./'`          | Path where jsCoq is installed.                                                                                |
| `wrapper_id`    | string          | `'ide-wrapper'` | Id of `<div>` element in which the jsCoq panel is to be created.                                              |
| `layout`        | string          | `'flex'`        | Choose between a flex-based layout (`'flex'`) and one based on fixed positioning (`'fixed'`).                 |
| `all_pkgs`      | array of string / object        | (see below)     | List of available packages that will be listed in the packages panel.                                         |
| `init_pkgs`     | array of string | `['init']`      | Packages to load at startup.                                                                                  |
| `init_import`   | array of string | `[]`            | Modules to `Require Import` on startup.                                                                       |
| `prelude`       | boolean         | `true`          | Load the Coq prelude (`Coq.Init.Prelude`) at startup. (If set, make sure that `init_pkgs` includes `'init'`.) |
| `implicit_libs` | boolean         | `false`         | Allow `Require`ing Coq built-in modules by short name only (e.g., `Require Arith.`).                          |
| `time`          | boolean         | `false`         | Print timing information for all sentences, as with `coqc -time`                                              |
| `theme`         | string          | `'light'`       | IDE theme to use; includes icon set and color scheme. Supported values are `'light'` and `'dark'`.            |
| `show`          | boolean         | `true`          | Opens up the jsCoq panel on startup.                                                                          |
| `focus`         | boolean         | `true`          | Sets the focus to the editor once jsCoq is ready.                                                             |
| `replace`       | boolean         | `false`         | Replace `<div>`(s) referred to by `jscoq_ids` with jsCoq editors, moving the text content.                    |
| `line_numbers`  | string          | `continue`      | Line numbering policy; across code snippets on page (`continue`) or separate per snippet (`restart`).         |
| `file_dialog`   | boolean         | `false`         | Enables UI for loading and saving files (^O/^S, or ⌘O/⌘S on Mac).                                             |
| `editor`        | object          | `{}`            | Additional options to be passed to CodeMirror.                                                                |
| `coq`           | object          | `{}`            | Additional Coq option values to be set at startup.                                                            |

The list of available packages defaults to all Coq libraries and addons
available with the current version of jsCoq. At the moment, it is:
```js
['init', 'coq-base', 'coq-collections', 'coq-arith', 'coq-reals',
 'math-comp', 'elpi', 'lf', 'plf']
```

By default, packages are loaded from jsCoq's `coq-pkgs` directory.
This can be controlled by passing an object instead of an array; the keys of
the object correspond to base directories where package files are located.
```js
{'../coq-pkgs': ['init', 'coq-base'], '/my-pkgs': ['cool-stuff']}
```

The `editor` property may contain any option supported by CodeMirror
(see [here](https://codemirror.net/doc/manual.html#config)).

The `coq` property may hold a list of Coq properties mapped to their
values, and is case sensitive (see [here](https://coq.inria.fr/refman/coq-optindex.html)).
For example:
```js
{'Implicit Arguments': true, 'Default Timeout': 10}
```

