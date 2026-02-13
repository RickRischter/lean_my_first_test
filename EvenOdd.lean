namespace LeanMyFirstTest

def Even (f: Int → Int): Prop:=
  ∀ x : Int, f (-x) = f (x)

def addFun (f g : Int → Int) : Int → Int :=
  fun x => f x + g x

theorem even_add {f g : Int -> Int}
  (hf : Even f) (hg : Even g) : Even (addFun f g) := by
  intro (x : Int)
  -- let k : Int → Int := addFun f g
  -- have hk : k = addFun f g := rfl
  rw [addFun, hf, hg]
  rfl

end LeanMyFirstTest
