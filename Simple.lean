import VersoManual
open Verso.Genre.Manual.InlineLean

#doc (Verso.Genre.Manual) "Index" =>

```lean
/- Test comment -/
example : 1 + 1 = 2 := by
  have : True := by sorry
  sorry
```

::::multilean
```lean
/- Multilean comment -/
example : 5 + 5 = 10 := by
```

Intermediate DemoTextbook

```lean
  let a := 5
  have : 5 = 5 := by
    omega
```

```lean
  let b := 5
  let c := 5
  sorry
```
::::
