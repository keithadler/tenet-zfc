/-
The worked example of the README's Quick start: `tenet-zfc run tests/fixtures/Example.lean --out example-out`.
An enumeration with a function on it, a polymorphic definition, and a theorem.
-/
inductive Color where
  | red | green | blue

def Color.next : Color → Color
  | .red => .green
  | .green => .blue
  | .blue => .red

def twice (f : α → α) (x : α) : α := f (f x)

theorem two_add_two : 2 + 2 = 4 := rfl
