Subject: [ANNOUNCE] jsCoq and SerAPI releases

Dear Coq users and developers,

we are happy to announce the releases of jsCoq 0.9.3 and SerAPI 0.6.1
for Coq 8.9.

JsCoq and SerAPI are free software, please don't hesitate to report
issues and contribute at:

- https://github.com/ejgallego/jscoq
- https://github.com/ejgallego/coq-serapi

## JsCoq 0.9:

JsCoq allows interacting with Coq developments as standard-compliant
HTML documents using a browser.  standard-compliant web pages. The
project aims to ease the development of interactive Coq documents and
teaching material, to improve the accessibility of the platform, and
to explore new user interaction possibilities.

jsCoq 0.9 has been three years in the making, and it features a long list
of improvements, most of them due to the incredible work of Shachar
Itzhaky, who managed to stabilize the Web Worker version and provided
countless usability and display improvements including
"Company-Coq"-like contextual information display facilities.

While there are still some minor bugs, we feel that this is the first
release that seems ready for wider testing and exposure; in
particular, as Coq now runs in a separate browser thread, the overall
experience is much smoother than before. Keep in mind that jsCoq's
primary target is introductory Coq material, thus it is expected to
struggle with heavy developments.

You can see some examples including the "Software Foundations" suite
in the links below:

- https://x80.org/rhino-coq/
- https://x80.org/rhino-coq/examples/lf/
- https://x80.org/rhino-coq/examples/plf/

See more examples and information in the project's web page
https://github.com/ejgallego/jscoq, the full list of changes is
at https://github.com/ejgallego/jscoq/blob/v8.9%2Bworker/CHANGES.md

## SerAPI 0.6.1

Coq-SerAPI provides an S-expression based API suitable for machine
interaction with Coq. Capabilities include full round-trip
serialization of Coq's AST and most internal structures, easy access
to the document build and checking API, and facilities for querying
Coq's environment and proof state.

The 0.6.1 release brings many improvements and features in the
serialization front. Thanks to the awesome efforts of Karl Palmskog
and Ahmet Celik, SerAPI is now able to serialize/deserialize large Coq
developments reliably, and we have improved the `sercomp` command-line
tool for batch (de)serialization of Coq files.

See more information and examples on the project's website
https://github.com/ejgallego/coq-serapi, the full list of changes is
at https://github.com/ejgallego/coq-serapi/blob/v8.9/CHANGES.md

Best regards,
Emilio & all contributors to these projects
