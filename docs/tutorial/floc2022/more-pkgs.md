# jsCoq Package Structure

It is very easy to use one of the *affiliated addon* libraries,
because they are recompiled and packaged by the jsCoq team on
every release.

```javascript
  const PKG_AFFILIATES = [  // Affiliated packages in @jscoq/@wacoq scope
    'mathcomp', 'elpi', 'equations', 'extlib', 'simpleio', 'quickchick', 
    'software-foundations',
    'hahn', 'paco', 'snu-sflib',
    'fcsl-pcm', 'htt', 'pnp', 'coqoban', 'stdpp', 'iris'
  ];
```

To install `mathcomp`, for example:
```
  npm i @jscoq/mathcomp@0.15.1
```

And add `'mathcomp'` to the `all_pkgs` options field.
See `res/footer.in.html` in this tutorial for an example.

Now you can do this:

```coq
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat div prime.

(* A nice proof of the infinitude of primes, by Georges Gonthier *)
Lemma prime_above m : {p | m < p & prime p}.
Proof.
  have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1
    by rewrite addn1 ltnS fact_gt0.
  exists p => //. rewrite ltnNge. apply: contraL p_dv_m1 => p_le_m.
  by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.
```

You may also want to compile your own `.v` files as libraries for use with jsCoq.
For example, this snippet uses a definition from `theories/CooLib.v`.

```coq
From FLoC Require Import CooLib.

Print Coo.
```

This can be achieved by compiling `theories/CooLib.v` with the
[jsCoq SDK](https://github.com/jscoq/jscoq/blob/v8.16/docs/authoring.md) and packaging it as a `.coq-pkg` using the jsCoq CLI.

See how it is done in this tutorial's `Makefile` (targets `%.vo` and `floc.coq-pkg`).