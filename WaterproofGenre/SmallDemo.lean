import WaterproofGenre
open Verso.Genre.Manual.InlineLean
-- test

#eval do
  IO.sleep 1000

#doc (Verso.Genre.Manual) "Index" =>

```lean
#eval do
  IO.sleep 1000
```


-- test
::::multilean

## ATC - 003

```lean
example : 1 + 1 = 2 := by
```

```lean
  have : 1 + 2 = 2 := by
    sorry
```

```lean
  have blah : 5 + 5 = 1 := by sorry
  have waah : True := by sorry

  sorry

#eval do
  IO.sleep 2000
```
::::

-- test
::::multilean

## ATC - 003

```lean
example : 1 + 1 = 2 := by
```

```lean
  have : 1 + 2 = 2 := by
    sorry
```

```lean
  have blah : 5 + 5 = 1 := by sorry
  have waah : True := by sorry

  sorry

#eval do
  IO.sleep 1000
```


::::
