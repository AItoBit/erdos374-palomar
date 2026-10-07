# Erdős 374: classical square products of factorials

Author and responsible maintainer: **alexander**. License: MIT.

This Lean development formalizes selected classical results associated with
[Erdős problem 374](https://www.erdosproblems.com/374) and Erdős–Graham,
[On products of factorials](https://combinatorica.hu/~p_erdos/1976-25.pdf),
Bull. Inst. Math. Acad. Sinica 4 (1976), **337–355**.
Its central conclusion is that every composite endpoint at least two admits
a square product of between two and six distinct positive factorials, and
therefore no minimum-cardinality class above six is populated. Prime endpoints
admit no representation. This is classical number theory, with a plausible
audience studying factorial Diophantine equations and formalized number theory.
No mathematical novelty is claimed.

The growth question for the minimum-cardinality classes is **not proved**.
`PositiveLowerDensitySix` merely defines the proposition that the six-factor
class has positive lower density. A recent
[preprint by Fedir Yudin, arXiv:2610.01899v1](https://arxiv.org/abs/2610.01899v1)
claims density results; these are not formalized here or independently audited.

## Mathematical definitions

`HasRep m k` says a finite set of exactly k distinct positive natural numbers
contains m, all its elements are at most m, and the product of their factorials
is a square in the natural numbers. `InD m k` additionally requires k ≥ 2 and
rules out every smaller cardinality ≥ 2. `D k` is the set of these endpoints.
`countD k n` counts endpoints in the closed interval [1,n]. Minimum cardinality
is relational: endpoints without a representation have no assigned minimum.

## Compared theorems

All eighteen declarations in namespace `Erdos374` are selected by Comparator.

| Declaration | Mathematical content |
| --- | --- |
| `rep_two` | Two positive distinct arguments with square factorial product give a two-factor representation. |
| `square_inD_two` | For r > 1, r² belongs to D₂, using arguments r²−1 and r². The converse is not proved. |
| `adjacent_identity` | For n > 0, n!(n−1)! = n((n−1)!)². |
| `four_factor_identity` | For positive r,u, the factorials at r²u,r²u−1,u,u−1 have a square product. No distinctness claim. |
| `six_factor_identity` | For positive a,b, factorials at ab,ab−1,a,a−1,b,b−1 have a square product. No minimality claim. |
| `minimum_unique` | An endpoint cannot have two different minimum cardinalities. |
| `prime_no_rep` | A prime endpoint has no representation, for any cardinality. |
| `product_separated_rep_six` | For a ≥ 2 and b ≥ a+2, the six construction arguments are distinct and give HasRep (ab) 6. |
| `product_adjacent_rep_four` | For a ≥ 2, the arguments a−1,a+1,a(a+1)−1,a(a+1) give a four-factor representation. |
| `product_equal_rep_two` | For a ≥ 2, a² has a two-factor representation. |
| `product_has_rep_le_six` | For a,b ≥ 2, ab has a representation with cardinality between two and six, splitting equal, adjacent, and separated factors. |
| `exists_minimum_le` | Any representation of cardinality k ≥ 2 gives an actual minimum of cardinality at most k. |
| `product_minimum_le_six` | For a,b ≥ 2, ab has an actual minimum no greater than six. |
| `rep_527_six` | 527=17·31 has a six-factor representation. Neither F(527)=6 nor its leastness in D₆ is proved. |
| `rep_card_le` | A representation at endpoint m has at most m positive distinct arguments. |
| `composite_minimum_le_six` | Every composite m ≥ 2 has an actual minimum no greater than six. |
| `D_empty_above_six` | D_k is empty for k > 6, using prime exclusion and the composite construction. |
| `countD_le` | For every k,n, countD k n ≤ n, the elementary counting upper bound. |

## Project and verification

`Erdos374.lean` contains the proof development supplied by the author, with
compatibility repairs documented in commit history. `Solution.lean` publicly
imports it. `Challenge.lean` independently repeats the definitions and theorem
types with deliberate proof holes, importing only pinned Mathlib modules.
The holes belong only to the statement module; the Solution must be checked
without `sorryAx`, custom axioms, or `Lean.ofReduceBool`.

Lean is pinned to v4.35.0-rc2; all dependencies have full commit pins in
`lake-manifest.json`. Build with `lake exe cache get` then `lake build`.
The GitHub Actions workflow calls Palomar's full reusable verifier, including
Comparator and NanoDa, at a fixed pipeline commit with `palomar-standard-v1`.
Its mechanical report is the source of verification status.

Codex assisted with submission packaging and compatibility repairs. Details
of original proof generation and independent human review were not supplied.
Authorship was confirmed by alexander. No previous formalization was identified
in the limited submission preparation search; this is not an exhaustive survey.
