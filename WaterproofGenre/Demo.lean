import WaterproofGenre
open WaterproofGenre

#doc (WaterproofGenre) "Index" =>

# Header

$$`x + y = z`

:::hint "Hint here"
This is a hint
:::


```lean
def a := 5
```

::::multilean
```lean
def hello :=
  "Hello, " ++
```

:::input
```lean
  "World" ++
```
:::

```lean
  "!"

#eval hello
```
::::

::::multilean
```lean
theorem test : 5 + 5 = 10 := by
```

:::input
```lean
  have : 1 + 2 = 3 := by

    sorry
```
:::

```lean
  sorry
```
::::
