import ICC.Praeludium
import Mathlib

namespace List

variable {α : Type*}

def cases {motive : List α → Sort*}
    (nil : motive [])
    (cons : (head : α) → (tail : List α) → motive (head :: tail))
    (t : List α) : motive t :=
  t.rec nil fun head tail _ ↦ cons head tail

end List

namespace Language

variable {α : Type*} [Bot α]

open Classical in
noncomputable def character (L : Language α) : List α → List α :=
  fun l ↦ if l ∈ L then [] else [⊥]

section character

variable {L : Language α} {l : List α}

@[simp] theorem character_eq_nil_iff :
    L.character l = [] ↔ l ∈ L := by simp [character]

@[simp] theorem character_eq_cons_zero_iff :
    L.character l = [⊥] ↔ l ∉ L := by simp [character]

@[simp] theorem character_ne_nil_iff :
    L.character l ≠ [] ↔ l ∉ L := by simp [character]

end character

open Matrix

variable (L : Language α)

inductive SafeFunction (L : Language α) :
    {n s : ℕ} → ((Fin n → List α) → (Fin s → List α) → List α) → Prop
  | oracle' :
    SafeFunction L fun (v : Fin 1 → List α) (_ : Fin 0 → List α) ↦
      L.character (vecHead v)
  | nil :
    SafeFunction L fun (_ : Fin 0 → List α) (_ : Fin 0 → List α) ↦ []
  | safe_cons' (a : α) :
    SafeFunction L fun (_ : Fin 0 → List α) (w : Fin 1 → List α) ↦ a :: vecHead w
  | safe_tail' :
    SafeFunction L fun (_ : Fin 0 → List α) (w : Fin 1 → List α) ↦ (vecHead w).tail
  | normal_proj {n s} (i : Fin n) :
    SafeFunction L fun (v : Fin n → List α) (_ : Fin s → List α) ↦ v i
  | safe_proj {n s} (i : Fin s) :
    SafeFunction L fun (_ : Fin n → List α) (w : Fin s → List α) ↦ w i
  | cond {n s}
    {f₀ : (Fin n → List α) → (Fin s → List α) → List α}
    {f : α → (Fin n → List α) → (Fin (s + 1) → List α) → List α}
    (hf₀ : SafeFunction L f₀)
    (hf : ∀ a, SafeFunction L (f a)) :
    SafeFunction L fun (v : Fin n → List α) (w : Fin (s + 1) → List α) ↦
      (vecHead w).cases (motive := fun _ ↦ List α) (f₀ v (vecTail w))
        fun head tail ↦ f head v (tail :> vecTail w)
  | safe_comp {n₁ n₂ s₁ s₂}
    {f : (Fin n₂ → List α) → (Fin s₂ → List α) → List α}
    {g : Fin n₂ → (Fin n₁ → List α) → (Fin 0 → List α) → List α}
    {h : Fin s₂ → (Fin n₁ → List α) → (Fin s₁ → List α) → List α}
    (hf : SafeFunction L f)
    (hg : ∀ i, SafeFunction L (g i))
    (hh : ∀ j, SafeFunction L (h j)) :
    SafeFunction L fun (v : Fin n₁ → List α) (w : Fin s₁ → List α) ↦
      f (g · v ![]) (h · v w)
  | safe_rec {n s}
    {f : (Fin n → List α) → (Fin s → List α) → List α}
    {g : α → (Fin (n + 1) → List α) → (Fin (s + 1) → List α) → List α}
    (hf : SafeFunction L f)
    (hg : ∀ a, SafeFunction L (g a)) :
    SafeFunction L fun (v : Fin (n + 1) → List α) (w : Fin s → List α) ↦
      (vecHead v).rec (f (vecTail v) w) fun head tail ih ↦
        g head (tail :> vecTail v) (vecCons ih w)

abbrev MvFeasible {n} (f : (Fin n → List α) → List α) : Prop :=
  L.SafeFunction fun v (_ : Fin 0 → List α) ↦ f v

abbrev Feasible (f : List α → List α) : Prop :=
  L.MvFeasible fun (v : Fin 1 → List α) ↦ f (vecHead v)

abbrev Feasible₂ (f : List α → List α → List α) : Prop :=
  L.MvFeasible fun (v : Fin 2 → List α) ↦ f (vecHead v) (vecHead (vecTail v))

attribute [fun_prop] SafeFunction MvFeasible Feasible Feasible₂

variable {L}

namespace SafeFunction

variable {n s : ℕ}

theorem of_eq {f g : (Fin n → List α) → (Fin s → List α) → List α}
    (hf : L.SafeFunction f) (h : ∀ v₁ v₂, g v₁ v₂ = f v₁ v₂) : L.SafeFunction g := by
  have : f = g := by grind
  rcases this; assumption

@[simp] theorem safe_vecHead :
    L.SafeFunction fun (_ : Fin n → List α) (w : Fin (s + 1) → List α) ↦ vecHead w := safe_proj 0

@[simp] theorem safe_cons (a : α) :
    L.SafeFunction fun (_ : Fin n → List α) (w : Fin (s + 1) → List α) ↦ a :: vecHead w :=
  safe_comp (safe_cons' a) (g := ![]) (by simp) (h := ![fun _ w ↦ vecHead w]) (by simp)

@[simp] theorem safe_tail :
    L.SafeFunction fun (_ : Fin n → List α) (w : Fin (s + 1) → List α) ↦ (vecHead w).tail :=
  safe_comp safe_tail' (g := ![]) (by simp) (h := ![fun _ w ↦ vecHead w]) (by simp)

@[simp] theorem const (l : List α) :
    L.SafeFunction fun (_ : Fin n → List α) (_ : Fin s → List α) ↦ l :=
  match l with
  |     [] => safe_comp (g := ![]) (h := ![]) nil (by simp) (by simp)
  | a :: l => safe_comp (g := ![]) (h := ![fun _ _ ↦ l])
    (safe_cons a) (by simp) (by simpa using const l)

theorem safe_append :
    L.SafeFunction fun (v : Fin (n + 1) → List α) (w : Fin (s + 1) → List α) ↦
      vecHead v ++ vecHead w := by
  apply of_eq <| SafeFunction.safe_rec safe_vecHead safe_cons
  suffices ∀ l₁ l₂ : List α, l₁ ++ l₂ = l₁.rec l₂ (fun head tail ih ↦ head :: ih) by
    intro v₁ v₂
    exact this (vecHead v₁) (vecHead v₂)
  intro l₁ l₂
  induction l₁ <;> simp [*]

end SafeFunction

namespace MvFeasible

variable {n : ℕ}

@[simp] theorem const (l : List α) :
    L.MvFeasible fun (_ : Fin n → List α) ↦ l := SafeFunction.const l

@[simp] theorem proj (i : Fin n) :
    L.MvFeasible fun v ↦ v i := SafeFunction.normal_proj i

@[simp] theorem vecHead :
    L.MvFeasible (n := n + 1) fun v ↦ vecHead v := proj 0

theorem comp {m} {f : (Fin m → List α) → List α} {g : Fin m → (Fin n → List α) → List α}
    (hf : L.MvFeasible f) (hg : ∀ i, L.MvFeasible (g i)) :
    L.MvFeasible fun v ↦ f (g · v) :=
  SafeFunction.safe_comp hf hg (h := ![]) (by simp)

end MvFeasible

namespace Feasible

variable {f g : List α → List α}

@[simp] protected theorem id : L.Feasible id := MvFeasible.proj 0

@[simp] theorem const (l : List α) : L.Feasible fun _ ↦ l := MvFeasible.const l

@[simp] theorem oracle : L.Feasible L.character := SafeFunction.oracle'

theorem comp (hf : L.Feasible f) (hg : L.Feasible g) : L.Feasible (f ∘ g) :=
  MvFeasible.comp hf (g := ![fun v ↦ g (vecHead v)]) (by simpa)

@[simp] theorem tail : L.Feasible List.tail :=
  SafeFunction.safe_comp
    SafeFunction.safe_tail (g := ![]) (by simp) (h := ![fun v _ ↦ vecHead v]) (by simp)

@[simp] theorem cons (a : α) : L.Feasible (List.cons a) :=
  SafeFunction.safe_comp
    (SafeFunction.safe_cons a) (g := ![]) (by simp) (h := ![fun v _ ↦ vecHead v]) (by simp)

end Feasible

namespace Feasible₂

theorem of_eq {f g : List α → List α → List α}
    (hf : L.Feasible₂ f) (h : ∀ v₁ v₂, g v₁ v₂ = f v₁ v₂) : L.Feasible₂ g := by
  have : f = g := by grind
  rcases this; assumption

theorem left : L.Feasible₂ fun v _ ↦ v := MvFeasible.proj 0

theorem right : L.Feasible₂ fun _ v ↦ v := MvFeasible.proj 1

theorem comp {f : List α → List α → List α} {g₁ g₂ : List α → List α}
    (hf : L.Feasible₂ f) (hg₁ : L.Feasible g₁) (hg₂ : L.Feasible g₂) :
    L.Feasible fun v ↦ f (g₁ v) (g₂ v) :=
  MvFeasible.comp hf
    (g := ![fun v ↦ g₁ (vecHead v), fun v ↦ g₂ (vecHead v)]) (by simpa using ⟨hg₁, hg₂⟩)

theorem append : L.Feasible₂ (· ++ ·) := by {  }

end Feasible₂

end Language
