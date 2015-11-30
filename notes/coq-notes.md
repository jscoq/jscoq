# Notes on Coq, and the Coq/API:

This document contains some random and incomplete information we
gathered on while working with Coq's API, as well as some constructive
;) comments and criticisms (marked with _fixme?_).

It is our view and it doesn't represent the views of the Coq Development team.

For the purposes of this commentary, we use a special-purpose branch
https://github.com/ejgallego/coq/tree/ejga-commentary so links to code
are stable.

## STM overview

Coq 8.5 has a new document model API called STM, which allows the
consumer to build Coq documents as a DAG. This enables much finer
control over Coq's processing of a document and makes writing
alternative frontends quite easier.

The current version is functional, but still not stable nor
complete. Also, some _technical debt_ and a fair amount of
compatibility code seems to be present; the Coq developers expect this
kind of code to progressively go away.

More details can be found in the ITP 2015 paper https://hal.inria.fr/hal-01135919

### STM Operation Overview

The basic idea of the STM API is to represent a Coq document as a
Directed Acyclic Graph, where edges are intended to represent the
dependency of each part of the document on previous parts, enabling
asynchronous/parallel processing.

The basic graph building operation is to `add` a statement to the
document; Coq will try to parse it, and if successful, a new node and
edges will be created by Coq representing the path from the root of
the three to that particular state. Every new node is assigned it an
unique _state id_.

Things are interesting sometimes: the core of Coq is very stateful and
some statements may produce _interesting_ side effects.

Document building is separated from document processing; we must tell
Coq that we want it to process the document up to a certain node, this
operation is named `observe`, and will make Coq try to process the
document up to the given _state id_.

Using pseudocode, a typical STM workflow of adding and processing one
new statement would be:

```
cur_state := Stm.init ()
while(new_input) {

  old_state := cur_state;

  try {
    cur_state := Stm.add(cur_state, new_input)

    try {
      Stm.observe(cur_state);
    } catch Error (..) {
      -- go back to the old state
         cur_state := old_state;
      -- Tell the STM to we want to edit a node
         Stm.edit_at(cur_state);
  } catch ParsingError(..) {
    -- Notify the user of a parse error.
  }
}
```

The last important piece of the API is the `edit_at` function: it
tells the STM that we are editing the tree from a particular node, so
all the successors become invalidated.

We have used `try ... catch ...` blocks to capture errors, but true
Coq error handling is more subtle, as Coq may both generate an
exception and call a hook too in order to report errors, command
completion, etc...

CoqIDE has a debug mode for showing the current document tree, it can
be invoked with:
```
$ coqide
```

### Basic Datatypes

The basic datatypes involved are:

* [`Stateid.t`](https://github.com/ejgallego/coq/blob/ejga-commentary/lib/stateid.mli)

  Abstract (private or opaque) type of state denoting a node in the
  document. This is the main type over which the `STM` works.

* [`edit_id`](https://github.com/ejgallego/coq/blob/ejga-commentary/lib/feedback.mli#L30-33)

  A user-controller integer to identify pre-parsed
  statements. `edit_id`'s are used for the cases the STM has not
  generated yet a state id (i.e: parsing errors).

* _fixme?_: There also exists an `edit_or_state_id` type, but it will
  be removed at some point.

* [`feedback`](https://github.com/ejgallego/coq/blob/ejga-commentary/lib/feedback.mli#L37-63)

  This type represents STM feedback. Currently, it includes very
  varied information.

  _fixme?_: Related to the previous fixme, it would be great to
  specialize the feedback type into more granular cases ensuring
  greater type safety and allowing the removal of the
  `edit_or_state_id` type.

* [`message`](https://github.com/ejgallego/coq/blob/ejga-commentary/lib/feedback.mli#L12-22)

  _fixme?_: This is the legacy feedback type, which doesn't include
  information about the particular node of the document it relates
  to. It is deprecated as should be gradually removed/encapsulated
  into a compat layer.

### Document Building

* [`add`](https://github.com/ejgallego/coq/blob/ejga-commentary/stm/stm.mli#L22-24)

  `add` builds a document by appending a new node.

   ```ocaml
(* [add ontop check vebose eid s] *)
val add : ontop:Stateid.t -> ?newtip:Stateid.t -> ?check:(located_vernac_expr -> unit) ->
  bool -> edit_id -> string ->
    Stateid.t * [ `NewTip | `Unfocus of Stateid.t ]
   ```

   It basically parses the input text and returns the new document
   id. If parsing fails, it will produce an exception and send
   feedback with the specified `edit_id`.

   `add` allows modular editing of the document. In the common case,
   it will return `NewTip`, as the newly added node is a leaf for the
   tree, however, if editing a document sub-part it will return
   `Unfocus` when the STM thinks that the sub-document has been closed
   (usually at QED time). See the `edit_at` and `observe`
   documentation for more information.

* [`edit_at`](https://github.com/ejgallego/coq/blob/ejga-commentary/stm/stm.mli#L40)

   ```ocaml
val edit_at : Stateid.t -> [ `NewTip | `Focus of focus ]
   ```

   The STM document model is stateful due to certain Coq commands
   having a global effect; thus, node editing ─ like in the case of an
   error or a user editing the document ─ must be globally signaled with `edit_at`.

   The argument of `edit_at` is the last known-good state we want to
   preserve. I will either return `NewTip`, signaling that new adds
   after the edit will become the new tip of the document, or `Focus`
   if the edit is "local" to the document, meaning that only depending
   parts of the graph will be discarded.

* [`observe`](https://github.com/ejgallego/coq/blob/ejga-commentary/stm/stm.mli#L45)

   ```ocaml
val observe : Stateid.t -> unit
   ```

   `add` and `edit_at` build the document, `observe` actually
   processes the document up to the specified `Stateid.t`.

   A good question is whether the processing is asynchronous or
   not. The general case is complicated due to Coq having too many
   commands, but a good rule of thumb is that if you do several `add`s
   followed by one observe, Coq will try to process the adds in
   parallel, whereas if the API user does add/observe in sync no
   parallel processing will take place.

   In order to enable async processing in CoqIDE, the _go to current
   point_ command can be used; then, CoqIDE will do a bunch of adds
   followed by a single observe.

   See `stm.ml:async_policy` for more information.
   (https://github.com/ejgallego/coq/blob/ejga-commentary/stm/stm.ml#L1637-1644)

* The STM API includes some more functions, such as:

   ```ocaml
val init : unit -> unit
val get_current_state : unit -> Stateid.t
   ```
  etc...

### Feedback

The main instrument the STM uses to communicate results of Coq
processing is the `feeeback` mechanism. Feedback tries to unify all
kinds of reporting, from debug and informative messages to error
handling. Previously, they were separated in Coq, with "informative"
output taken care of by printing functions and error handling mainly
done via exceptions.

As noted in the coq sources, the current implementation seems a bit in
flux due to compatibility constraints.

Feedback related operations are split among three modules:

* [`Feedback`](https://github.com/ejgallego/coq/blob/ejga-commentary/lib/feedback.mli)

  Datatype definition and serialization occur here.

* [`Pp`](https://github.com/ejgallego/coq/blob/ejga-commentary/lib/pp.mli#L164)

  Surprisingly, the main functions used by Coq to generate feedback
  are located here for legacy reasons.

  The first part of such functions is composed by the old-style
  `msg_*` functions, used to output messages to `stdout/stderr`. They
  still do, unless `log_via_feedback()` is called, which will pipe
  them through a feedback message.

  The main feedback producer function ─ that is, the way Coq internals generate feedback ─ is:
  [`feedback`](https://github.com/ejgallego/coq/blob/ejga-commentary/lib/pp.mli#L175-178)

  ```ocaml
val feedback :
  ?state_id:Feedback.state_id -> ?edit_id:Feedback.edit_id ->
  ?route:Feedback.route_id -> Feedback.feedback_content -> unit
  ```

  which produces the corresponding feedback.

  _fixme_: There is a precondition on `feedback` imposing that only
  one of `state_id` or `edit_id` can be set at call time, this should
  be fixed soon.

  Feedback consumers may register with:

   ```ocaml
val set_feeder : (Feedback.feedback -> unit) -> unit
   ```

  It seems that only one consumer can be registered.

* [`Stm`](https://github.com/ejgallego/coq/blob/ejga-commentary/stm/stm.mli#L97)

  Aside from the general feedback mechanism, `Stm` provides
  finer-grained `Hooks` for some crucial events:

   ```ocaml
val state_computed_hook    : (Stateid.t -> in_cache:bool -> unit) Hook.t
val parse_error_hook       : (Feedback.edit_or_state_id -> Loc.t -> Pp.std_ppcmds -> unit) Hook.t
val execution_error_hook   : (Stateid.t -> Loc.t -> Pp.std_ppcmds -> unit) Hook.t
val unreachable_state_hook : (Stateid.t -> unit) Hook.t
val state_ready_hook       : (Stateid.t -> unit) Hook.t
   ```

   By default, this functions will just call `feedback` with an
   appropriate constructor (usually `MsgError`) but ideally their
   implementation would be made mandatory by the API users and, as
   noted before, adapted to a specialized `feedback` type.

### More on Feedback

A possibility for the future of async STM feedback in Coq could be to
have a "dispatch" module where users may register for particular
events. Event generation should replace all the `msg_*` functions in
`Pp`.

Several dispatch modules should be allowed to coexist, and they they
should be thread local, but that is another issue.

### Error handling.

Due to legacy constraints, error handling and reporting currently has
some overlap between the new feedback mechanism and Ocaml exceptions.

This is not a big problem, but care must be taken when interacting
with the STM API.

The approach CoqIDE takes is to wrap all the exceptions, see
[`ide_slave.ml`](https://github.com/ejgallego/coq/blob/ejga-commentary/ide/ide_slave.ml#L327)

The error hooks in `Feedback` are set by default to send `ErrorMsg` feedback messages.

Some of exceptions an STM user is allowed to/must catch are:

```ocaml
[in errors.mli]
exception UserError of string * std_ppcmds
exception AlreadyDeclared of std_ppcmds

[in proofs.ml etc...]
exception NoSuchProof
exception NoCurrentProof
exception FailedBullet of t * suggestion
```

## Settable Vernacular Options

Vernacular Options (as `Set Printing All`) are defined and accessed
using the
[`Goptions`](https://github.com/ejgallego/coq/blob/ejga-commentary/library/goptions.mli)
module.

An option declared through this interface can perform any arbitrary
global action. This seems quite inconvenient and IMVHO should be
addressed.

Strangely enough, it seems that there is no easy way in the API to
query what the status of an option is.

## Other (minor) comments

### VM static initializers

`vm.ml` does a lot of static initialization. This is not good for a
wide variety of reasons, and very inconvenient for jscoq.

### Declare ML Module

`Declare ML Module` is unqualified, which is a bit inconvenient for
applications like jscoq that have to manage their own fs layout.

