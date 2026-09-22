#  Proving the book Transitions and Trees by Hans Hüttel in Agda
INCOMPLETE.
Progress is page 66 out of 267.

## Conventions
All files are camel-case (HereIsAnExample), except that the first character's case has meaning:
1. Uppercase: This file is a library file, meaning it can not import example files.
2. Lowercase: This file is an example file, meaning it can import anything and can be imported by other example files.

## Contribution
Feel free to contribute. I'm going through the book in order. To contribute, you can look for the latest page. Since page numbers are commented above and below (hopefully) all code, you can look for the biggest page number and prove/define the next thing that isn't proven/defined.

## Mistakes found in the book
Mistakes mentioned in the [errata](http://www.operationalsemantics.net/errata.pdf) (meaning the official corrections) won't be repeated here.

Author uses PLUS and SUB in tandom in the small-step transition rules for Aexp, when it should be ADD and SUB, or PLUS and MINUS. Found at Table 3.2.

Bexp on Table 3.4 defines the rule EQUALS-1BSS. Bexp on Table 4.2 defines EQUAL-1BSS. There is a leading S after EQUAL in one case, and not the other.

In Table 4.2, the rule PARENT-BBSS has 2 'B's, which could be intentional but I doubt it.

In page 31, under `3.3 Big-step vs small-step semantics`, it states that a small-step semantics's transition rule does not need to result in a terminal configuration, which is not a restriction. Therefore the set of semantics that are SmallStepSemantics is equal to the set of all transition systems.

Problem 4.9 uses `>`, which is not defined, only `<` is defined.

Theorem 4.11, in step comp-BSS, in the last sentence, it is assumed that `x ⇒* y` and `y ⇒* z` means you can do `x ⇒* z`. It is true, but no axiom or rule is invoked.

Theorem 4.11, in step while-false-BSS, IF-FALSK-SSS isn't defined. Seems to be an accidental use of the danish "falsk" instead of "false".

Theorem 4.11, in step while-false-BSS, in the conclusion, the first `⇒*` should be a `⇒`.

Lemma 4.12 assumes that the transition sequence `a⇒b⇒ᵏc` can be rewritten as `a⇒⟨S,s⟩⇒ᵏc`, which is a mistake, `b` can also be a state. Trivially fixed by proving this case.

Theorem 4.13 at the start of page 59 assumes that the transition sequence `a⇒b⇒ᵏc` can be rewritten as `a⇒⟨S,s⟩⇒ᵏc`, which is a mistake, `b` can also be a state. Trivially fixed by proving this case.

Lemma 4.14 has ⟨S₁;S₂⟩⇒ᵏs˝, which isn't a valid statement, state in left side is omitted.

Lemma 4.14, sentence "k₂ = k₂₂". k₂₂ is never defined, only k₂₁, which I have assumed the author meant.

Table 9.1 generalized variables, two different rules are given the same name "GVAR-1BSS".

### Opinionated
The generic transition ⇒ᵏ in transition systems I believe would be simpler if instead of defining it using step 0 and step suc k, and defining ⇒* afterwards, you could just define ⇒* first. Every induction, instead of being reliant on an integer, could just rely on the length of the transition sequence itself. The reason I believe this is simpler is that it avoids the duplicate information from k, since it's determined by the transition sequence anyways. Duplicate information is annoying when unifying things. It could be that I only believe this because Agda proves by construction, and needs unification a lot.

In the proof of Theorem 4.13, there's a form of referencing done for the sentence "transition sequence (4.11)", which isn't done before this point, where parenthesis referencing their definition is done. This implicitly applies the lemma 4.11. It is, in my opinion, confusing to introduce new syntax never before defined or mentioned.

Theorem 4.13 only proves 2 out of the 5 cases (see "We show only two cases here") and yet is called a proof in the book. It isn't a proof, because a proof requires proving all sub cases when proving by construction. This is opinionated, because "We show only two cases here" could be implicitly assuming the other 3 cases as some sort of axioms, though it's pretty impropper, imo.

Theorem 4.13 defines s˝´ and yet re-uses s˝. They are equal, so not a mistake, but the proof in Theorem 4.13 proves for s˝, which only works if you assume they are equal. It is an implicit assumption.

The book never defines which set theory it assumes.

Table 3.2 and 4.1 have identical descriptions but different content. Both claim to be transition rules for Aexp but the two "Aexp"s are different.
