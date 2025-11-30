import Mathlib

namespace Matrix

open Fin

variable {n : ℕ} {α : Type*}

infixr:70 " :> " => vecCons

@[simp] theorem vecHead_vecCons_nil_eq_self (v : Fin 1 → α) : vecHead v :> ![] = v := by
  ext i; simp [Fin.fin_one_eq_zero i]; rfl

end Matrix
