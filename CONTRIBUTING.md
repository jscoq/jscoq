## Contributing to jsCoq

Thanks for willing to contribute to jsCoq! Contributing is as easy as
opening a pull request, issue, or dropping by the Gitter channel and
talking to us.

### Coding style

Nothing very special has to be kept in mind, we follow standard OCaml
practice, with `ocp-indent` and `ocamlformat` indentation guidelines,
but we are liberal in some places, in particular with regards to
intra-line indentation. We compile with a very strict set of warnings.

### Review and merge guidelines

We recommend that most non-trivial changes take place using pull
requests. Any contributor can merge a pull request [including their
own] provided the pull request:

- has updated the `CHANGES.md` file,
- passes Travis CI,
- has been reviewed if needed.

Note that we'd like to favor an agile development style, and remain
liberal in merging PRs.

While one approving review from other contributor is encouraged before
merging, feel free to go ahead if you are confident the change is
correct, if a review doesn't happen in a reasonable amount of time, or
if delaying the merge would interfere with your development plans.

We prefer GPG signed commits as well as `Signed-off-by` commits.

### Commit tag conventions [work in progress]:

We have some [soft] commit tag conventions:

- [jscoq]: ML/Coq interface
- [ui]: Html/Css commit
- [cm]: CodeMirror provider
- [libs]: Coq Library support and format
- [doc]: Documentation
- [addons]: Addons support
- [build]: Build system
- [feature]: Adding a new feature
- [bugfix]: Bug fix
- [refactor]: Refactoring commit (no functional change intended)
- [ci] / [travis]: Continuous integration
- [test]: Adding or modifying a test
- [misc]: Miscellanenous small things
