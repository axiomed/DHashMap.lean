/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
universe u v w w'
namespace Lean

/-- List-like type to avoid extra level of indirection, with dependent types on it. -/
inductive DAssocList (α : Type u) (β : α → Type v) where
  | nil : DAssocList α β
  | cons (key : α) (value : β key) (tail : DAssocList α β) : DAssocList α β
  deriving Inhabited

namespace DAssocList
variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

abbrev empty : DAssocList α β :=
  nil

instance : EmptyCollection (DAssocList α β) := ⟨empty⟩

abbrev insert (m : DAssocList α β) (k : α) (v : β k) : DAssocList α β :=
  m.cons k v

def isEmpty : DAssocList α β → Bool
  | nil => true
  | _   => false

@[specialize] def foldlM (f : δ → (k: α) → β k → m δ) : (init : δ) → DAssocList α β → m δ
  | d, nil         => pure d
  | d, cons a b es => do
    let d ← f d a b
    foldlM f d es

@[inline] def foldl (f : δ → (k: α) → β k → δ) (init : δ) (as : DAssocList α β) : δ :=
  Id.run (foldlM f init as)

def toList (as : DAssocList α β) : List (Sigma β) :=
  as.foldl (init := []) (fun r a b => ⟨a, b⟩::r) |>.reverse

@[specialize] def forM (f : (k: α) → β k → m PUnit) : DAssocList α β → m PUnit
  | nil         => pure ⟨⟩
  | cons a b es => do f a b; forM f es


def findEntry? [BEq α] (a : α) : DAssocList α β → Option (Sigma β)
  | nil         => none
  | cons k v es => match k == a with
    | true  => some ⟨k, v⟩
    | false => findEntry? a es

def find? [DecidableEq α] (a : α) : DAssocList α β → Option (β a)
  | nil         => none
  | cons k v es =>
    if h: k = a
      then some (h ▸ v)
      else find? a es

def contains [BEq α] (a : α) : DAssocList α β → Bool
  | nil         => false
  | cons k _ es => k == a || contains a es

def replace [BEq α] (a : α) (b : β a) : DAssocList α β → DAssocList α β
  | nil         => nil
  | cons k v es => match k == a with
    | true  => cons a b es
    | false => cons k v (replace a b es)

def erase [BEq α] (a : α) : DAssocList α β → DAssocList α β
  | nil         => nil
  | cons k v es => match k == a with
    | true  => es
    | false => cons k v (erase a es)

def any (p : (k: α) → β k → Bool) : DAssocList α β → Bool
  | nil         => false
  | cons k v es => p k v || any p es

def all (p : (k: α) → β k → Bool) : DAssocList α β → Bool
  | nil         => true
  | cons k v es => p k v && all p es

@[inline] protected def forIn {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w'} [Monad m]
    (as : DAssocList α β) (init : δ) (f : (Sigma β) → δ → m (ForInStep δ)) : m δ :=
  let rec @[specialize] loop
    | d, nil => pure d
    | d, cons k v es => do
      match (← f ⟨k, v⟩ d) with
      | ForInStep.done d  => pure d
      | ForInStep.yield d => loop d es
  loop init as

instance : ForIn m (DAssocList α β) (Sigma β) where
  forIn := DAssocList.forIn

end Lean.DAssocList

def List.toDAssocList' {α : Type u} {β : α → Type v} : List (Sigma β) → Lean.DAssocList α β
  | []          => Lean.DAssocList.nil
  | ⟨a,b⟩ :: es => Lean.DAssocList.cons a b (toDAssocList' es)
