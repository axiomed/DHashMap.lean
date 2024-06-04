/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

import DHashMap.DAssocList
import Lean

namespace Lean

def DHashMapBucket (α : Type u) (β : α → Type v) :=
  { b : Array (DAssocList α β) // b.size.isPowerOfTwo }

def DHashMapBucket.update {α : Type u} {β : α → Type v} (data : DHashMapBucket α β) (i : USize) (d : DAssocList α β) (h : i.toNat < data.val.size) : DHashMapBucket α β :=
  ⟨ data.val.uset i d h,
    by erw [Array.size_set]; apply data.property ⟩

structure DHashMapImp (α : Type u) (β : α → Type v) where
  size       : Nat
  buckets    : DHashMapBucket α β

private def numBucketsForCapacity (capacity : Nat) : Nat :=
  -- a "load factor" of 0.75 is the usual standard for hash maps
  capacity * 4 / 3

def mkDHashMapImp {α : Type u} {β : α → Type v} (capacity := 8) : DHashMapImp α β :=
  { size       := 0
    buckets    :=
    ⟨mkArray (numBucketsForCapacity capacity).nextPowerOfTwo DAssocList.nil,
     by simp; apply Nat.isPowerOfTwo_nextPowerOfTwo⟩ }

namespace DHashMapImp
variable {α : Type u} {β : α → Type v}

/- Remark: we use a C implementation because this function is performance critical. -/
@[extern "lean_hashmap_mk_idx"]
private def mkIdx {sz : Nat} (hash : UInt64) (h : sz.isPowerOfTwo) : { u : USize // u.toNat < sz } :=
  -- TODO: avoid `if` in the reference implementation
  let u := hash.toUSize &&& (sz.toUSize - 1)
  if h' : u.toNat < sz then
    ⟨u, h'⟩
  else
    ⟨0, by simp [USize.toNat, OfNat.ofNat, USize.ofNat, Fin.ofNat']; apply Nat.pos_of_isPowerOfTwo h⟩

@[inline] def reinsertAux (hashFn : α → UInt64) (data : DHashMapBucket α β) (a : α) (b : β a) : DHashMapBucket α β :=
  let ⟨i, h⟩ := mkIdx (hashFn a) data.property
  data.update i (DAssocList.cons a b data.val[i]) h

@[inline] def foldBucketsM {δ : Type w} {m : Type w → Type w} [Monad m] (data : DHashMapBucket α β) (d : δ) (f : δ → (x: α) → β x → m δ) : m δ :=
  data.val.foldlM (init := d) fun d b => b.foldlM f d

@[inline] def foldBuckets {δ : Type w} (data : DHashMapBucket α β) (d : δ) (f : δ → (x: α) → β x → δ) : δ :=
  Id.run $ foldBucketsM data d f

@[inline] def foldM {δ : Type w} {m : Type w → Type w} [Monad m] (f : δ → (x: α) → β x → m δ) (d : δ) (h : DHashMapImp α β) : m δ :=
  foldBucketsM h.buckets d f

@[inline] def fold {δ : Type w} (f : δ → (x: α) → β x → δ) (d : δ) (m : DHashMapImp α β) : δ :=
  foldBuckets m.buckets d f

@[inline] def forBucketsM {m : Type w → Type w} [Monad m] (data : DHashMapBucket α β) (f : (x: α) → β x → m PUnit) : m PUnit :=
  data.val.forM fun b => b.forM f

@[inline] def forM {m : Type w → Type w} [Monad m] (f : (x: α) → β x → m PUnit) (h : DHashMapImp α β) : m PUnit :=
  forBucketsM h.buckets f

def findEntry? [BEq α] [Hashable α] (m : DHashMapImp α β) (a : α) : Option (Sigma β) :=
  match m with
  | ⟨_, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx (hash a) buckets.property
    buckets.val[i].findEntry? a

def find? [beq : DecidableEq α] [Hashable α] (m : DHashMapImp α β) (a : α) : Option (β a) :=
  match m with
  | ⟨_, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx (hash a) buckets.property
    buckets.val[i].find? a

def contains [BEq α] [Hashable α] (m : DHashMapImp α β) (a : α) : Bool :=
  match m with
  | ⟨_, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx (hash a) buckets.property
    buckets.val[i].contains a

def moveEntries [Hashable α] (i : Nat) (source : Array (DAssocList α β)) (target : DHashMapBucket α β) : DHashMapBucket α β :=
  if h : i < source.size then
     let idx : Fin source.size := ⟨i, h⟩
     let es  : DAssocList α β   := source.get idx
     -- We remove `es` from `source` to make sure we can reuse its memory cells when performing es.foldl
     let source                := source.set idx DAssocList.nil
     let target                := es.foldl (reinsertAux hash) target
     moveEntries (i+1) source target
  else target
termination_by source.size - i

def expand [Hashable α] (size : Nat) (buckets : DHashMapBucket α β) : DHashMapImp α β :=
  let bucketsNew : DHashMapBucket α β := ⟨
    mkArray (buckets.val.size * 2) DAssocList.nil,
    by simp; apply Nat.mul2_isPowerOfTwo_of_isPowerOfTwo buckets.property
  ⟩
  { size    := size,
    buckets := moveEntries 0 buckets.val bucketsNew }

@[inline] def insert [beq : BEq α] [Hashable α] (m : DHashMapImp α β) (a : α) (b : β a) : DHashMapImp α β × Bool :=
  match m with
  | ⟨size, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx (hash a) buckets.property
    let bkt    := buckets.val[i]
    if bkt.contains a then
      (⟨size, buckets.update i (bkt.replace a b) h⟩, true)
    else
      let size'    := size + 1
      let buckets' := buckets.update i (DAssocList.cons a b bkt) h
      if numBucketsForCapacity size' ≤ buckets.val.size then
        ({ size := size', buckets := buckets' }, false)
      else
        (expand size' buckets', false)

def erase [BEq α] [Hashable α] (m : DHashMapImp α β) (a : α) : DHashMapImp α β :=
  match m with
  | ⟨ size, buckets ⟩ =>
    let ⟨i, h⟩ := mkIdx (hash a) buckets.property
    let bkt    := buckets.val[i]
    if bkt.contains a then ⟨size - 1, buckets.update i (bkt.erase a) h⟩
    else m

inductive WellFormed [BEq α] [Hashable α] : DHashMapImp α β → Prop where
  | mkWff     : ∀ n,                    WellFormed (mkDHashMapImp n)
  | insertWff : ∀ m a b, WellFormed m → WellFormed (insert m a b |>.1)
  | eraseWff  : ∀ m a,   WellFormed m → WellFormed (erase m a)

end DHashMapImp

def DHashMap (α : Type u) (β : α → Type v) [BEq α] [Hashable α] :=
  { m : DHashMapImp α β // m.WellFormed }

open Lean.DHashMapImp

def mkDHashMap {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (capacity := 8) : DHashMap α β :=
  ⟨ mkDHashMapImp capacity, WellFormed.mkWff capacity ⟩

namespace DHashMap
instance [BEq α] [Hashable α] : Inhabited (DHashMap α β) where
  default := mkDHashMap

instance [BEq α] [Hashable α] : EmptyCollection (DHashMap α β) := ⟨mkDHashMap⟩

@[inline] def empty [BEq α] [Hashable α] : DHashMap α β :=
  mkDHashMap

variable {α : Type u} {β : α → Type v} {_ : BEq α} {_ : Hashable α}

def insert (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  match m with
  | ⟨ m, hw ⟩ =>
    match h:m.insert a b with
    | (m', _) => ⟨ m', by have aux := WellFormed.insertWff m a b hw; rw [h] at aux; assumption ⟩

/-- Similar to `insert`, but also returns a Boolean flad indicating whether an existing entry has been replaced with `a -> b`. -/
def insert' (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Bool :=
  match m with
  | ⟨ m, hw ⟩ =>
    match h:m.insert a b with
    | (m', replaced) => (⟨ m', by have aux := WellFormed.insertWff m a b hw; rw [h] at aux; assumption ⟩, replaced)

@[inline] def erase (m : DHashMap α β) (a : α) : DHashMap α β :=
  match m with
  | ⟨ m, hw ⟩ => ⟨ m.erase a, WellFormed.eraseWff m a hw ⟩

@[inline] def findEntry? (m : DHashMap α β) (a : α) : Option (Sigma β) :=
  match m with
  | ⟨ m, _ ⟩ => m.findEntry? a

@[inline] def find? [DecidableEq α] (m : DHashMap α β) (a : α) : Option (β a) :=
  match m with
  | ⟨ m, _ ⟩ => m.find? a

@[inline] def findD [DecidableEq α] (m : DHashMap α β) (a : α) (b₀ : β a) : β a :=
  (m.find? a).getD b₀

@[inline] def find! [DecidableEq α] (m : DHashMap α β) (a : α)[Inhabited (β a)] : β a :=
  match m.find? a with
  | some b => b
  | none   => panic! "key is not in the map"

@[inline] def contains (m : DHashMap α β) (a : α) : Bool :=
  match m with
  | ⟨ m, _ ⟩ => m.contains a

@[inline] def foldM {δ : Type w} {m : Type w → Type w} [Monad m] (f : δ → (x: α) → β x → m δ) (init : δ) (h : DHashMap α β) : m δ :=
  match h with
  | ⟨ h, _ ⟩ => h.foldM f init

@[inline] def fold {δ : Type w} (f : δ → (x: α) → β x → δ) (init : δ) (m : DHashMap α β) : δ :=
  match m with
  | ⟨ m, _ ⟩ => m.fold f init

@[inline] def forM {m : Type w → Type w} [Monad m] (f : (x: α) → β x → m PUnit) (h : DHashMap α β) : m PUnit :=
  match h with
  | ⟨ h, _ ⟩ => h.forM f

@[inline] def size (m : DHashMap α β) : Nat :=
  match m with
  | ⟨ {size := sz, ..}, _ ⟩ => sz

@[inline] def isEmpty (m : DHashMap α β) : Bool :=
  m.size = 0

def toList (m : DHashMap α β) : List (Sigma β) :=
  m.fold (init := []) fun r k v => ⟨k, v⟩::r

def toArray (m : DHashMap α β) : Array (Sigma β) :=
  m.fold (init := #[]) fun r k v => r.push ⟨k, v⟩

def numBuckets (m : DHashMap α β) : Nat :=
  m.val.buckets.val.size

/-- Builds a `DHashMap` from a list of key-value pairs. Values of duplicated keys are replaced by their respective last occurrences. -/
def ofList (l : List (Sigma β)) : DHashMap α β :=
  l.foldl (init := DHashMap.empty) (fun m p => m.insert p.fst p.snd)

/-- Variant of `ofList` which accepts a function that combines values of duplicated keys. -/
def ofListWith [DecidableEq α] (l : List (Sigma β)) (f : (x: α) → β x → β x → β x) : DHashMap α β :=
  l.foldl (init := DHashMap.empty)
    (fun m p =>
      match m.find? p.fst with
        | none   => m.insert p.fst p.snd
        | some v => m.insert p.fst $ f p.fst v p.snd)
end Lean.DHashMap
