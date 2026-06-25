-- Combined entry point for exercise sheets that use both the WaterproofGenre
-- document genre and Verbose Lean tactics.
--
-- Requires the package to be built with the `dev` environment flag:
--   lake build -K env=dev WaterproofGenreVerbose
import WaterproofGenre
import Verbose.English.All

open WaterproofGenre
open Verbose.NameLess

#doc (WaterproofGenre) "Index" =>

::::multilean
```lean
Example "1.1.1"
  Given: (a b c : ℤ)
  Assume: (_ : c ∣ b) (_ : b ∣ a)
  Conclusion: c ∣ a
Proof:
  Since c ∣ b we get n such that b = c * n
  Since b ∣ a we get m such that a = b * m
  Let's prove that n * m works
  Calc
    a = (c * n) * m since a = b * m and b = c * n
    _ = c * (n * m) by computation
QED
```
::::

::::multilean
```lean
Example "1.1.8"
  Given: (p q r : Prop)
  Assume: (_ : p) (_ : q) (_ : r)
  Conclusion: (p ∧ q) ∧ r
Proof:
```
:::input
```lean
  Let's first prove that p ∧ q
  · Let's first prove that p
    · We conclude by hypothesis
    Let's now prove that q
    · We conclude by hypothesis
  Let's now prove that r
  · We conclude by hypothesis
```
:::
```lean
QED
```
::::


::::multilean
```lean
Example "1.1.11"
  Given: (p q : Prop)
  Assume: (_ : p ∧ q)
  Conclusion: q ∧ p
Proof:
```
:::input
```lean
  sorry
```
:::
```lean
QED
```
::::

::::multilean
```lean
Example "test"
  Given: (p q : Prop)
  Assume: (_ : p ∧ q)
  Conclusion: ∀ x : ℝ, q ∧ p
Proof:
```
:::input
```lean

```
:::
```lean
QED
```
::::
