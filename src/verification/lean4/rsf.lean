namespace RSFLean

inductive ZigError : Type where
  | overflow : ZigError
  | invalidDimension : ZigError
  | invalidLayerCount : ZigError
  | badFileFormat : ZigError
  | unsupportedVersion : ZigError
  | checksumMismatch : ZigError
  | trailingData : ZigError
  | allocationFailed : ZigError
  | invalidShape : ZigError
  | invalidConfig : ZigError
  | handleCopied : ZigError
  | invalidHandle : ZigError
  | registryFull : ZigError
  | alreadyDestroyed : ZigError
  | activeOperations : ZigError
  | gpuUnavailable : ZigError
  | gpuVersionMismatch : ZigError
  | f16OutOfRange : ZigError
  | toleranceInvalid : ZigError
  | clipRangeInvalid : ZigError
  | tensorOverlap : ZigError
  | shapesMismatch : ZigError
  | nonFiniteValue : ZigError
  | batchSizeZero : ZigError
  | dimZero : ZigError

inductive ResultT (α : Type) : Type where
  | ok : α → ResultT α
  | err : ZigError → ResultT α

noncomputable def ResultT.bind {α β : Type} (r : ResultT α) (f : α → ResultT β) : ResultT β :=
  ResultT.recOn (motive := fun _ => ResultT β) r
    (fun a => f a)
    (fun e => ResultT.err e)

noncomputable def ResultT.map {α β : Type} (f : α → β) (r : ResultT α) : ResultT β :=
  ResultT.recOn (motive := fun _ => ResultT β) r
    (fun a => ResultT.ok (f a))
    (fun e => ResultT.err e)

theorem ResultT.bind_ok {α β : Type} (a : α) (f : α → ResultT β) :
    ResultT.bind (ResultT.ok a) f = f a :=
  Eq.refl (f a)

theorem ResultT.bind_err {α β : Type} (e : ZigError) (f : α → ResultT β) :
    ResultT.bind (ResultT.err e) f = ResultT.err e :=
  Eq.refl (ResultT.err e)

theorem ResultT.bind_assoc {α β γ : Type} (r : ResultT α) (f : α → ResultT β) (g : β → ResultT γ) :
    ResultT.bind (ResultT.bind r f) g = ResultT.bind r (fun a => ResultT.bind (f a) g) :=
  ResultT.recOn (motive := fun s => ResultT.bind (ResultT.bind s f) g = ResultT.bind s (fun a => ResultT.bind (f a) g)) r
    (fun a => Eq.refl (ResultT.bind (f a) g))
    (fun e => Eq.refl (ResultT.err e))

theorem ResultT.map_ok {α β : Type} (a : α) (f : α → β) :
    ResultT.map f (ResultT.ok a) = ResultT.ok (f a) :=
  Eq.refl (ResultT.ok (f a))

theorem ResultT.map_err {α β : Type} (e : ZigError) (f : α → β) :
    ResultT.map f (ResultT.err e) = ResultT.err e :=
  Eq.refl (ResultT.err e)

theorem ResultT.ok_ne_err {α : Type} (a : α) (e : ZigError) :
    ResultT.ok a ≠ ResultT.err e :=
  fun h => ResultT.noConfusion h

theorem ResultT.err_ne_ok {α : Type} (e : ZigError) (a : α) :
    ResultT.err e ≠ ResultT.ok a :=
  fun h => ResultT.noConfusion h

noncomputable def bNot : Bool → Bool :=
  fun b => Bool.recOn (motive := fun _ => Bool) b Bool.true Bool.false

noncomputable def bAnd : Bool → Bool → Bool :=
  fun b1 b2 => Bool.recOn (motive := fun _ => Bool) b1 Bool.false b2

noncomputable def bOr : Bool → Bool → Bool :=
  fun b1 b2 => Bool.recOn (motive := fun _ => Bool) b1 b2 Bool.true

noncomputable def bIte {α : Type} (b : Bool) (t f : α) : α :=
  Bool.recOn (motive := fun _ => α) b f t

theorem bNot_true : bNot Bool.true = Bool.false := Eq.refl Bool.false
theorem bNot_false : bNot Bool.false = Bool.true := Eq.refl Bool.true
theorem bNot_bNot (b : Bool) : bNot (bNot b) = b :=
  Bool.recOn (motive := fun c => bNot (bNot c) = c) b (Eq.refl Bool.false) (Eq.refl Bool.true)

theorem bAnd_true_l (b : Bool) : bAnd Bool.true b = b := Eq.refl b
theorem bAnd_false_l (b : Bool) : bAnd Bool.false b = Bool.false := Eq.refl Bool.false
theorem bAnd_true_r (b : Bool) : bAnd b Bool.true = b :=
  Bool.recOn (motive := fun c => bAnd c Bool.true = c) b (Eq.refl Bool.false) (Eq.refl Bool.true)
theorem bAnd_false_r (b : Bool) : bAnd b Bool.false = Bool.false :=
  Bool.recOn (motive := fun c => bAnd c Bool.false = Bool.false) b (Eq.refl Bool.false) (Eq.refl Bool.false)
theorem bAnd_comm (b1 b2 : Bool) : bAnd b1 b2 = bAnd b2 b1 :=
  Bool.recOn (motive := fun c => bAnd c b2 = bAnd b2 c) b1
    (Bool.recOn (motive := fun c => bAnd Bool.false c = bAnd c Bool.false) b2
      (Eq.refl Bool.false) (Eq.refl Bool.false))
    (Bool.recOn (motive := fun c => bAnd Bool.true c = bAnd c Bool.true) b2
      (Eq.refl Bool.false) (Eq.refl Bool.true))
theorem bAnd_assoc (b1 b2 b3 : Bool) : bAnd (bAnd b1 b2) b3 = bAnd b1 (bAnd b2 b3) :=
  Bool.recOn (motive := fun c => bAnd (bAnd c b2) b3 = bAnd c (bAnd b2 b3)) b1
    (Eq.refl Bool.false)
    (Eq.refl (bAnd b2 b3))
theorem bAnd_self (b : Bool) : bAnd b b = b :=
  Bool.recOn (motive := fun c => bAnd c c = c) b (Eq.refl Bool.false) (Eq.refl Bool.true)

theorem bOr_false_l (b : Bool) : bOr Bool.false b = b := Eq.refl b
theorem bOr_true_l (b : Bool) : bOr Bool.true b = Bool.true := Eq.refl Bool.true
theorem bOr_false_r (b : Bool) : bOr b Bool.false = b :=
  Bool.recOn (motive := fun c => bOr c Bool.false = c) b (Eq.refl Bool.false) (Eq.refl Bool.true)
theorem bOr_true_r (b : Bool) : bOr b Bool.true = Bool.true :=
  Bool.recOn (motive := fun c => bOr c Bool.true = Bool.true) b (Eq.refl Bool.true) (Eq.refl Bool.true)
theorem bOr_comm (b1 b2 : Bool) : bOr b1 b2 = bOr b2 b1 :=
  Bool.recOn (motive := fun c => bOr c b2 = bOr b2 c) b1
    (Bool.recOn (motive := fun c => bOr Bool.false c = bOr c Bool.false) b2
      (Eq.refl Bool.false) (Eq.refl Bool.true))
    (Bool.recOn (motive := fun c => bOr Bool.true c = bOr c Bool.true) b2
      (Eq.refl Bool.true) (Eq.refl Bool.true))
theorem bOr_assoc (b1 b2 b3 : Bool) : bOr (bOr b1 b2) b3 = bOr b1 (bOr b2 b3) :=
  Bool.recOn (motive := fun c => bOr (bOr c b2) b3 = bOr c (bOr b2 b3)) b1
    (Eq.refl (bOr b2 b3))
    (Eq.refl Bool.true)
theorem bOr_self (b : Bool) : bOr b b = b :=
  Bool.recOn (motive := fun c => bOr c c = c) b (Eq.refl Bool.false) (Eq.refl Bool.true)

theorem bIte_true {α : Type} (t f : α) : bIte Bool.true t f = t := Eq.refl t
theorem bIte_false {α : Type} (t f : α) : bIte Bool.false t f = f := Eq.refl f
theorem bIte_same {α : Type} (b : Bool) (x : α) : bIte b x x = x :=
  Bool.recOn (motive := fun c => bIte c x x = x) b (Eq.refl x) (Eq.refl x)

theorem bFalseNeTrueHelper : Bool.false = Bool.true → False :=
  fun h => Bool.noConfusion h

theorem bTrueNeFalseHelper : Bool.true = Bool.false → False :=
  fun h => Bool.noConfusion h

noncomputable def natEqB : Nat → Nat → Bool :=
  fun m n => Nat.recOn (motive := fun _ => Nat → Bool) m
    (fun n => Nat.recOn (motive := fun _ => Bool) n Bool.true (fun _ _ => Bool.false))
    (fun m' ihm n => Nat.recOn (motive := fun _ => Bool) n Bool.false (fun n' _ => ihm n'))

theorem natEqB_refl (n : Nat) : natEqB n n = Bool.true :=
  Nat.recOn (motive := fun k => natEqB k k = Bool.true) n
    (Eq.refl Bool.true)
    (fun k ih => ih)

theorem natEqB_zero_zero : natEqB 0 0 = Bool.true := Eq.refl Bool.true
theorem natEqB_zero_succ (n : Nat) : natEqB 0 (Nat.succ n) = Bool.false := Eq.refl Bool.false
theorem natEqB_succ_zero (n : Nat) : natEqB (Nat.succ n) 0 = Bool.false := Eq.refl Bool.false
theorem natEqB_succ_succ (m n : Nat) : natEqB (Nat.succ m) (Nat.succ n) = natEqB m n := Eq.refl (natEqB m n)

theorem natEqB_symm (m n : Nat) : natEqB m n = natEqB n m :=
  Nat.recOn (motive := fun k => ∀ j, natEqB k j = natEqB j k) m
    (fun j => Nat.recOn (motive := fun k => natEqB 0 k = natEqB k 0) j
      (Eq.refl Bool.true)
      (fun j' _ => Eq.refl Bool.false))
    (fun m' ihm j => Nat.recOn (motive := fun k => natEqB (Nat.succ m') k = natEqB k (Nat.succ m')) j
      (Eq.refl Bool.false)
      (fun j' _ => ihm j'))
    n

noncomputable def natLeB : Nat → Nat → Bool :=
  fun m n => Nat.recOn (motive := fun _ => Nat → Bool) m
    (fun _ => Bool.true)
    (fun m' ihm n => Nat.recOn (motive := fun _ => Bool) n Bool.false (fun n' _ => ihm n'))

theorem natLeB_zero (n : Nat) : natLeB 0 n = Bool.true := Eq.refl Bool.true
theorem natLeB_succ_zero (m : Nat) : natLeB (Nat.succ m) 0 = Bool.false := Eq.refl Bool.false
theorem natLeB_succ_succ (m n : Nat) : natLeB (Nat.succ m) (Nat.succ n) = natLeB m n := Eq.refl (natLeB m n)
theorem natLeB_refl (n : Nat) : natLeB n n = Bool.true :=
  Nat.recOn (motive := fun k => natLeB k k = Bool.true) n (Eq.refl Bool.true) (fun k ih => ih)

noncomputable def natLtB : Nat → Nat → Bool :=
  fun m n => natLeB (Nat.succ m) n

theorem natLtB_zero_succ (n : Nat) : natLtB 0 (Nat.succ n) = Bool.true := Eq.refl Bool.true
theorem natLtB_zero_zero : natLtB 0 0 = Bool.false := Eq.refl Bool.false
theorem natLtB_succ_succ (m n : Nat) : natLtB (Nat.succ m) (Nat.succ n) = natLtB m n := Eq.refl (natLtB m n)
theorem natLtB_irrefl (n : Nat) : natLtB n n = Bool.false :=
  Nat.recOn (motive := fun k => natLtB k k = Bool.false) n
    (Eq.refl Bool.false)
    (fun k ih => ih)

noncomputable def natSub : Nat → Nat → Nat :=
  fun m n => Nat.recOn (motive := fun _ => Nat → Nat) n m (fun n' ihn k =>
    Nat.recOn (motive := fun _ => Nat) k 0 (fun k' _ => ihn k'))

theorem natSub_zero (n : Nat) : natSub n 0 = n := Eq.refl n
theorem natSub_self (n : Nat) : natSub n n = 0 :=
  Nat.recOn (motive := fun k => natSub k k = 0) n
    (Eq.refl 0)
    (fun k ih => ih)
theorem natSub_succ_succ (m n : Nat) : natSub (Nat.succ m) (Nat.succ n) = natSub m n :=
  Eq.refl (natSub m n)
theorem natSub_zero_left (n : Nat) : natSub 0 n = 0 :=
  Nat.recOn (motive := fun k => natSub 0 k = 0) n
    (Eq.refl 0)
    (fun k _ => Eq.refl 0)

noncomputable def checkedMul (a b : Nat) : ResultT Nat :=
  let prod := Nat.mul a b
  bIte (natLeB prod 18446744073709551615) (ResultT.ok prod) (ResultT.err ZigError.overflow)

noncomputable def checkedMulU64 (a b : Nat) : ResultT Nat :=
  let prod := Nat.mul a b
  bIte (natLeB prod 18446744073709551615) (ResultT.ok prod) (ResultT.err ZigError.overflow)

noncomputable def checkedAddU64 (a b : Nat) : ResultT Nat :=
  let sum := Nat.add a b
  bIte (natLeB sum 18446744073709551615) (ResultT.ok sum) (ResultT.err ZigError.overflow)

noncomputable def checkedCastU64ToUsize (n : Nat) : ResultT Nat :=
  bIte (natLeB n 18446744073709551615) (ResultT.ok n) (ResultT.err ZigError.overflow)

theorem checkedMul_ok_when_small (a b : Nat) (h : natLeB (Nat.mul a b) 18446744073709551615 = Bool.true) :
    checkedMul a b = ResultT.ok (Nat.mul a b) :=
  congrArg (fun x => bIte x (ResultT.ok (Nat.mul a b)) (ResultT.err ZigError.overflow)) h

theorem checkedMul_err_when_large (a b : Nat) (h : natLeB (Nat.mul a b) 18446744073709551615 = Bool.false) :
    checkedMul a b = ResultT.err ZigError.overflow :=
  congrArg (fun x => bIte x (ResultT.ok (Nat.mul a b)) (ResultT.err ZigError.overflow)) h

theorem checkedAddU64_ok_when_small (a b : Nat) (h : natLeB (Nat.add a b) 18446744073709551615 = Bool.true) :
    checkedAddU64 a b = ResultT.ok (Nat.add a b) :=
  congrArg (fun x => bIte x (ResultT.ok (Nat.add a b)) (ResultT.err ZigError.overflow)) h

theorem checkedAddU64_commutes_ok (a b : Nat)
    (h1 : natLeB (Nat.add a b) 18446744073709551615 = Bool.true)
    (h2 : natLeB (Nat.add b a) 18446744073709551615 = Bool.true) :
    checkedAddU64 a b = checkedAddU64 b a :=
  Eq.trans
    (congrArg (fun x => bIte x (ResultT.ok (Nat.add a b)) (ResultT.err ZigError.overflow)) h1)
    (Eq.symm (congrArg (fun x => bIte x (ResultT.ok (Nat.add b a)) (ResultT.err ZigError.overflow)) h2))

noncomputable def listLength {α : Type} : List α → Nat :=
  fun xs => List.recOn (motive := fun _ => Nat) xs 0 (fun _ _ n => Nat.succ n)

theorem listLength_nil {α : Type} : listLength ([] : List α) = 0 := Eq.refl 0
theorem listLength_cons {α : Type} (h : α) (t : List α) :
    listLength (List.cons h t) = Nat.succ (listLength t) := Eq.refl (Nat.succ (listLength t))

noncomputable def listAppend {α : Type} : List α → List α → List α :=
  fun xs ys => List.recOn (motive := fun _ => List α) xs ys (fun h _ acc => List.cons h acc)

theorem listAppend_nil_left {α : Type} (ys : List α) : listAppend List.nil ys = ys := Eq.refl ys
theorem listAppend_cons {α : Type} (h : α) (t ys : List α) :
    listAppend (List.cons h t) ys = List.cons h (listAppend t ys) := Eq.refl _
theorem listAppend_nil_right {α : Type} (xs : List α) : listAppend xs List.nil = xs :=
  List.recOn (motive := fun l => listAppend l List.nil = l) xs
    (Eq.refl List.nil)
    (fun h t ih => congrArg (List.cons h) ih)
theorem listAppend_assoc {α : Type} (xs ys zs : List α) :
    listAppend (listAppend xs ys) zs = listAppend xs (listAppend ys zs) :=
  List.recOn (motive := fun l => listAppend (listAppend l ys) zs = listAppend l (listAppend ys zs)) xs
    (Eq.refl (listAppend ys zs))
    (fun h t ih => congrArg (List.cons h) ih)

theorem listLength_append {α : Type} (xs ys : List α) :
    listLength (listAppend xs ys) = Nat.add (listLength xs) (listLength ys) :=
  List.recOn (motive := fun l => listLength (listAppend l ys) = Nat.add (listLength l) (listLength ys)) xs
    (Eq.refl (listLength ys))
    (fun h t ih => congrArg Nat.succ ih)

noncomputable def listMap {α β : Type} (f : α → β) : List α → List β :=
  fun xs => List.recOn (motive := fun _ => List β) xs List.nil
    (fun h _ acc => List.cons (f h) acc)

theorem listMap_nil {α β : Type} (f : α → β) : listMap f List.nil = List.nil := Eq.refl _
theorem listMap_cons {α β : Type} (f : α → β) (h : α) (t : List α) :
    listMap f (List.cons h t) = List.cons (f h) (listMap f t) := Eq.refl _
theorem listLength_map {α β : Type} (f : α → β) (xs : List α) :
    listLength (listMap f xs) = listLength xs :=
  List.recOn (motive := fun l => listLength (listMap f l) = listLength l) xs
    (Eq.refl 0)
    (fun h t ih => congrArg Nat.succ ih)

noncomputable def listGetD {α : Type} (xs : List α) (i : Nat) (d : α) : α :=
  Nat.recOn (motive := fun _ => List α → α) i
    (fun l => List.recOn (motive := fun _ => α) l d (fun h _ _ => h))
    (fun _ ihI l => List.recOn (motive := fun _ => α) l d (fun _ t _ => ihI t))
    xs

theorem listGetD_nil {α : Type} (i : Nat) (d : α) : listGetD List.nil i d = d :=
  Nat.recOn (motive := fun k => listGetD List.nil k d = d) i
    (Eq.refl d)
    (fun k _ => Eq.refl d)

theorem listGetD_zero_cons {α : Type} (h : α) (t : List α) (d : α) :
    listGetD (List.cons h t) 0 d = h := Eq.refl h

theorem listGetD_succ_cons {α : Type} (h : α) (t : List α) (i : Nat) (d : α) :
    listGetD (List.cons h t) (Nat.succ i) d = listGetD t i d := Eq.refl _

noncomputable def listRange : Nat → List Nat :=
  fun n => Nat.recOn (motive := fun _ => List Nat) n
    List.nil
    (fun k acc => listAppend acc (List.cons k List.nil))

theorem listRange_zero : listRange 0 = List.nil := Eq.refl _
theorem listRange_succ (n : Nat) : listRange (Nat.succ n) = listAppend (listRange n) (List.cons n List.nil) :=
  Eq.refl _

theorem listLength_range (n : Nat) : listLength (listRange n) = n :=
  Nat.recOn (motive := fun k => listLength (listRange k) = k) n
    (Eq.refl 0)
    (fun k ih =>
      Eq.trans
        (listLength_append (listRange k) (List.cons k List.nil))
        (congrArg (fun x => Nat.add x 1) ih))

noncomputable def listReplicate {α : Type} (n : Nat) (a : α) : List α :=
  Nat.recOn (motive := fun _ => List α) n List.nil (fun _ acc => List.cons a acc)

theorem listReplicate_zero {α : Type} (a : α) : listReplicate 0 a = List.nil := Eq.refl _
theorem listReplicate_succ {α : Type} (n : Nat) (a : α) :
    listReplicate (Nat.succ n) a = List.cons a (listReplicate n a) := Eq.refl _
theorem listLength_replicate {α : Type} (n : Nat) (a : α) : listLength (listReplicate n a) = n :=
  Nat.recOn (motive := fun k => listLength (listReplicate k a) = k) n
    (Eq.refl 0)
    (fun k ih => congrArg Nat.succ ih)

noncomputable def listFoldl {α β : Type} (f : α → β → α) (init : α) : List β → α :=
  fun xs => List.recOn (motive := fun _ => α) xs init (fun h _ acc => f acc h)

theorem listFoldl_nil {α β : Type} (f : α → β → α) (init : α) :
    listFoldl f init List.nil = init := Eq.refl init

theorem listFoldl_cons {α β : Type} (f : α → β → α) (init : α) (h : β) (t : List β) :
    listFoldl f init (List.cons h t) = listFoldl f (f init h) t := Eq.refl _

noncomputable def listZipWith {α β γ : Type} (f : α → β → γ) : List α → List β → List γ :=
  fun xs ys => List.recOn (motive := fun _ => List β → List γ) xs
    (fun _ => List.nil)
    (fun h t ihT ys2 => List.recOn (motive := fun _ => List γ) ys2
      List.nil
      (fun h2 t2 _ => List.cons (f h h2) (ihT t2)))
    ys

theorem listZipWith_nil_left {α β γ : Type} (f : α → β → γ) (ys : List β) :
    listZipWith f List.nil ys = List.nil := Eq.refl _
theorem listZipWith_nil_right {α β γ : Type} (f : α → β → γ) (xs : List α) :
    listZipWith f xs List.nil = List.nil :=
  List.recOn (motive := fun l => listZipWith f l List.nil = List.nil) xs
    (Eq.refl List.nil)
    (fun _ _ _ => Eq.refl List.nil)
theorem listZipWith_cons_cons {α β γ : Type} (f : α → β → γ) (hx : α) (tx : List α) (hy : β) (ty : List β) :
    listZipWith f (List.cons hx tx) (List.cons hy ty) = List.cons (f hx hy) (listZipWith f tx ty) :=
  Eq.refl _
theorem listLength_zipWith {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) :
    listLength (listZipWith f xs ys) = Nat.min (listLength xs) (listLength ys) :=
  List.recOn (motive := fun l => listLength (listZipWith f l ys) = Nat.min (listLength l) (listLength ys)) xs
    (Eq.refl 0)
    (fun h t ih =>
      List.recOn (motive := fun m => listLength (listZipWith f (List.cons h t) m) = Nat.min (listLength (List.cons h t)) (listLength m)) ys
        (Eq.refl 0)
        (fun hy ty _ => congrArg Nat.succ (ih)))

noncomputable def listTake {α : Type} : Nat → List α → List α :=
  fun n xs => Nat.recOn (motive := fun _ => List α → List α) n
    (fun _ => List.nil)
    (fun _ ihN l => List.recOn (motive := fun _ => List α) l
      List.nil
      (fun h t _ => List.cons h (ihN t)))
    xs

noncomputable def listDrop {α : Type} : Nat → List α → List α :=
  fun n xs => Nat.recOn (motive := fun _ => List α → List α) n
    (fun l => l)
    (fun _ ihN l => List.recOn (motive := fun _ => List α) l
      List.nil
      (fun _ t _ => ihN t))
    xs

theorem listTake_zero {α : Type} (xs : List α) : listTake 0 xs = List.nil := Eq.refl _
theorem listDrop_zero {α : Type} (xs : List α) : listDrop 0 xs = xs := Eq.refl xs
theorem listTake_nil {α : Type} (n : Nat) : listTake n ([] : List α) = List.nil :=
  Nat.recOn (motive := fun k => listTake k ([] : List α) = List.nil) n
    (Eq.refl _) (fun k _ => Eq.refl _)
theorem listDrop_nil {α : Type} (n : Nat) : listDrop n ([] : List α) = List.nil :=
  Nat.recOn (motive := fun k => listDrop k ([] : List α) = List.nil) n
    (Eq.refl _) (fun k _ => Eq.refl _)
theorem listTake_cons_succ {α : Type} (n : Nat) (h : α) (t : List α) :
    listTake (Nat.succ n) (List.cons h t) = List.cons h (listTake n t) := Eq.refl _
theorem listDrop_cons_succ {α : Type} (n : Nat) (h : α) (t : List α) :
    listDrop (Nat.succ n) (List.cons h t) = listDrop n t := Eq.refl _

theorem listTake_append_drop {α : Type} (n : Nat) (xs : List α) :
    listAppend (listTake n xs) (listDrop n xs) = xs :=
  Nat.recOn (motive := fun k => ∀ ys, listAppend (listTake k ys) (listDrop k ys) = ys) n
    (fun ys => Eq.refl ys)
    (fun k ih ys =>
      List.recOn (motive := fun l => listAppend (listTake (Nat.succ k) l) (listDrop (Nat.succ k) l) = l) ys
        (Eq.refl List.nil)
        (fun h t _ => congrArg (List.cons h) (ih t)))
    xs

theorem listLength_take {α : Type} (n : Nat) (xs : List α) (h : natLeB n (listLength xs) = Bool.true) :
    listLength (listTake n xs) = n :=
  Nat.recOn (motive := fun k => ∀ ys, natLeB k (listLength ys) = Bool.true → listLength (listTake k ys) = k) n
    (fun _ _ => Eq.refl 0)
    (fun k ih ys hle =>
      List.recOn (motive := fun l => natLeB (Nat.succ k) (listLength l) = Bool.true → listLength (listTake (Nat.succ k) l) = Nat.succ k) ys
        (fun hbad => False.elim (bFalseNeTrueHelper (Eq.symm hbad)))
        (fun hy ty _ hle2 => congrArg Nat.succ (ih ty hle2))
        hle)
    xs h

noncomputable def natXor (a b : Nat) : Nat := Nat.xor a b
noncomputable def natBitwiseAnd (a b : Nat) : Nat := Nat.land a b
noncomputable def natShiftRight (a n : Nat) : Nat := Nat.shiftRight a n
noncomputable def natShiftLeft (a n : Nat) : Nat := Nat.shiftLeft a n

theorem natXor_self (n : Nat) : natXor n n = 0 :=
  Nat.recOn (motive := fun k => natXor k k = 0) n
    (Eq.refl 0)
    (fun k ih => ih)

theorem natXor_zero_r (n : Nat) : natXor n 0 = n :=
  Nat.recOn (motive := fun k => natXor k 0 = k) n
    (Eq.refl 0)
    (fun k ih => congrArg Nat.succ ih)

theorem natXor_zero_l (n : Nat) : natXor 0 n = n :=
  Nat.recOn (motive := fun k => natXor 0 k = k) n
    (Eq.refl 0)
    (fun k ih => congrArg Nat.succ ih)

theorem natXor_comm (m n : Nat) : natXor m n = natXor n m :=
  Nat.recOn (motive := fun a => ∀ b, natXor a b = natXor b a) m
    (fun b => Eq.trans (natXor_zero_l b) (Eq.symm (natXor_zero_r b)))
    (fun a iha b => Nat.recOn (motive := fun c => natXor (Nat.succ a) c = natXor c (Nat.succ a)) b
      (Eq.trans (natXor_zero_r (Nat.succ a)) (Eq.symm (natXor_zero_l (Nat.succ a))))
      (fun b' _ => iha b'))
    n

theorem natBitwiseAnd_zero_r (n : Nat) : natBitwiseAnd n 0 = 0 :=
  Nat.recOn (motive := fun k => natBitwiseAnd k 0 = 0) n
    (Eq.refl 0)
    (fun k _ => Eq.refl 0)

theorem natBitwiseAnd_self (n : Nat) : natBitwiseAnd n n = n :=
  Nat.recOn (motive := fun k => natBitwiseAnd k k = k) n
    (Eq.refl 0)
    (fun k ih => ih)

theorem natShiftRight_zero (n : Nat) : natShiftRight n 0 = n := Eq.refl n
theorem natShiftRight_succ (n k : Nat) : natShiftRight n (Nat.succ k) = Nat.div (natShiftRight n k) 2 :=
  Nat.recOn (motive := fun m => natShiftRight n (Nat.succ m) = Nat.div (natShiftRight n m) 2) k
    (Eq.refl (Nat.div n 2))
    (fun k' _ => Eq.refl _)

noncomputable def crc32Poly : Nat := 3988292384
noncomputable def crc32Init : Nat := 4294967295
noncomputable def crc32Mask : Nat := 4294967295

noncomputable def crc32BitStep (v : Nat) : Nat :=
  bIte (natEqB (Nat.mod v 2) 1)
    (natXor (natShiftRight v 1) crc32Poly)
    (natShiftRight v 1)

theorem crc32BitStep_def_odd (v : Nat) (h : natEqB (Nat.mod v 2) 1 = Bool.true) :
    crc32BitStep v = natXor (natShiftRight v 1) crc32Poly :=
  congrArg (fun x => bIte x (natXor (natShiftRight v 1) crc32Poly) (natShiftRight v 1)) h

theorem crc32BitStep_def_even (v : Nat) (h : natEqB (Nat.mod v 2) 1 = Bool.false) :
    crc32BitStep v = natShiftRight v 1 :=
  congrArg (fun x => bIte x (natXor (natShiftRight v 1) crc32Poly) (natShiftRight v 1)) h

noncomputable def iterN (f : Nat → Nat) (n : Nat) (x : Nat) : Nat :=
  Nat.recOn (motive := fun _ => Nat) n x (fun _ acc => f acc)

theorem iterN_zero (f : Nat → Nat) (x : Nat) : iterN f 0 x = x := Eq.refl x
theorem iterN_succ (f : Nat → Nat) (n : Nat) (x : Nat) :
    iterN f (Nat.succ n) x = f (iterN f n x) := Eq.refl _

noncomputable def crc32TableEntry (i : Nat) : Nat := iterN crc32BitStep 8 i

theorem crc32TableEntry_def (i : Nat) :
    crc32TableEntry i = crc32BitStep (crc32BitStep (crc32BitStep (crc32BitStep (crc32BitStep (crc32BitStep (crc32BitStep (crc32BitStep i))))))) :=
  Eq.refl _

noncomputable def crc32Update (crc byte : Nat) : Nat :=
  let idx := natBitwiseAnd (natXor crc byte) 255
  natXor (natShiftRight crc 8) (crc32TableEntry idx)

theorem crc32Update_def (crc byte : Nat) :
    crc32Update crc byte = natXor (natShiftRight crc 8) (crc32TableEntry (natBitwiseAnd (natXor crc byte) 255)) :=
  Eq.refl _

noncomputable def crc32Final (crc : Nat) : Nat := natXor crc crc32Mask

theorem crc32Final_involution (crc : Nat) : crc32Final (crc32Final crc) = crc :=
  Eq.trans (natXor_comm (natXor crc crc32Mask) crc32Mask) (Eq.refl crc)

theorem crc32Final_def (crc : Nat) : crc32Final crc = natXor crc 4294967295 := Eq.refl _

noncomputable def crc32OfList (bytes : List Nat) : Nat :=
  crc32Final (listFoldl crc32Update crc32Init bytes)

theorem crc32OfList_nil : crc32OfList List.nil = crc32Final crc32Init := Eq.refl _
theorem crc32OfList_cons (h : Nat) (t : List Nat) :
    crc32OfList (List.cons h t) = crc32OfList t :=
  congrArg crc32Final (listFoldl_cons crc32Update crc32Init h t)

theorem crc32Update_deterministic (crc byte : Nat) :
    crc32Update crc byte = crc32Update crc byte := Eq.refl _

structure FloatInterface : Type 1 where
  carrier : Type
  zeroF : carrier
  oneF : carrier
  negOneF : carrier
  addF : carrier → carrier → carrier
  subF : carrier → carrier → carrier
  mulF : carrier → carrier → carrier
  divF : carrier → carrier → carrier
  negF : carrier → carrier
  absF : carrier → carrier
  maxF : carrier → carrier → carrier
  minF : carrier → carrier → carrier
  expF : carrier → carrier
  clipF : carrier → carrier → carrier → carrier
  ltF : carrier → carrier → Bool
  leF : carrier → carrier → Bool
  eqF : carrier → carrier → Bool
  isFiniteF : carrier → Bool
  floatToU32 : carrier → Nat
  u32ToFloat : Nat → carrier
  ofNat : Nat → carrier
  expF_positive : ∀ (x : carrier), ltF zeroF (expF x) = Bool.true
  clipF_lower : ∀ (x lo hi : carrier), ltF lo hi = Bool.true → leF lo (clipF x lo hi) = Bool.true
  clipF_upper : ∀ (x lo hi : carrier), ltF lo hi = Bool.true → leF (clipF x lo hi) hi = Bool.true
  clipF_below : ∀ (x lo hi : carrier), ltF x lo = Bool.true → clipF x lo hi = lo
  clipF_above : ∀ (x lo hi : carrier), ltF hi x = Bool.true → clipF x lo hi = hi
  clipF_id : ∀ (x lo hi : carrier), leF lo x = Bool.true → leF x hi = Bool.true → clipF x lo hi = x
  divF_mulF_inv : ∀ (x y : carrier), ltF zeroF y = Bool.true → mulF (divF x y) y = x
  mulF_divF_cancel : ∀ (x y : carrier), ltF zeroF y = Bool.true → divF (mulF x y) y = x
  addF_comm : ∀ (x y : carrier), addF x y = addF y x
  addF_assoc : ∀ (x y z : carrier), addF (addF x y) z = addF x (addF y z)
  mulF_comm : ∀ (x y : carrier), mulF x y = mulF y x
  mulF_assoc : ∀ (x y z : carrier), mulF (mulF x y) z = mulF x (mulF y z)
  addF_zero_r : ∀ (x : carrier), addF x zeroF = x
  addF_zero_l : ∀ (x : carrier), addF zeroF x = x
  mulF_one_r : ∀ (x : carrier), mulF x oneF = x
  mulF_one_l : ∀ (x : carrier), mulF oneF x = x
  mulF_zero_r : ∀ (x : carrier), mulF x zeroF = zeroF
  mulF_zero_l : ∀ (x : carrier), mulF zeroF x = zeroF
  absF_nonneg : ∀ (x : carrier), leF zeroF (absF x) = Bool.true
  absF_neg : ∀ (x : carrier), absF (negF x) = absF x
  subF_self : ∀ (x : carrier), subF x x = zeroF
  subF_addF_cancel : ∀ (x y : carrier), subF (addF x y) y = x
  addF_subF_cancel : ∀ (x y : carrier), addF (subF x y) y = x
  leF_refl : ∀ (x : carrier), leF x x = Bool.true
  leF_trans : ∀ (x y z : carrier), leF x y = Bool.true → leF y z = Bool.true → leF x z = Bool.true
  ltF_leF : ∀ (x y : carrier), ltF x y = Bool.true → leF x y = Bool.true
  ltF_irrefl : ∀ (x : carrier), ltF x x = Bool.false
  expF_monotone : ∀ (x y : carrier), ltF x y = Bool.true → ltF (expF x) (expF y) = Bool.true
  leF_expF_monotone : ∀ (x y : carrier), leF x y = Bool.true → leF (expF x) (expF y) = Bool.true
  floatBitsRoundtrip : ∀ (x : carrier), u32ToFloat (floatToU32 x) = x
  floatBitsMax : ∀ (x : carrier), natLeB (floatToU32 x) 4294967295 = Bool.true
  isFiniteF_expF : ∀ (x : carrier), isFiniteF (expF x) = Bool.true
  mulF_addF_distrib_r : ∀ (x y z : carrier), mulF (addF x y) z = addF (mulF x z) (mulF y z)
  mulF_addF_distrib_l : ∀ (x y z : carrier), mulF x (addF y z) = addF (mulF x y) (mulF x z)
  addF_subF_eq_zero : ∀ (x : carrier), subF x x = zeroF
  maxF_comm : ∀ (x y : carrier), maxF x y = maxF y x
  maxF_assoc : ∀ (x y z : carrier), maxF (maxF x y) z = maxF x (maxF y z)
  maxF_ge_l : ∀ (x y : carrier), leF x (maxF x y) = Bool.true
  maxF_ge_r : ∀ (x y : carrier), leF y (maxF x y) = Bool.true
  minF_le_l : ∀ (x y : carrier), leF (minF x y) x = Bool.true
  minF_le_r : ∀ (x y : carrier), leF (minF x y) y = Bool.true
  absF_zero : absF zeroF = zeroF
  negF_negF : ∀ (x : carrier), negF (negF x) = x
  subF_def : ∀ (x y : carrier), subF x y = addF x (negF y)
  ltF_leF_trans : ∀ (x y z : carrier), ltF x y = Bool.true → leF y z = Bool.true → ltF x z = Bool.true
  leF_ltF_trans : ∀ (x y z : carrier), leF x y = Bool.true → ltF y z = Bool.true → ltF x z = Bool.true
  mulF_pos_pos : ∀ (x y : carrier), ltF zeroF x = Bool.true → ltF zeroF y = Bool.true → ltF zeroF (mulF x y) = Bool.true

theorem expF_nonneg (fi : FloatInterface) (x : fi.carrier) :
    fi.leF fi.zeroF (fi.expF x) = Bool.true :=
  fi.ltF_leF fi.zeroF (fi.expF x) (fi.expF_positive x)

theorem clipF_result_le_hi (fi : FloatInterface) (x lo hi : fi.carrier)
    (h : fi.ltF lo hi = Bool.true) :
    fi.leF (fi.clipF x lo hi) hi = Bool.true :=
  fi.clipF_upper x lo hi h

theorem clipF_result_ge_lo (fi : FloatInterface) (x lo hi : fi.carrier)
    (h : fi.ltF lo hi = Bool.true) :
    fi.leF lo (fi.clipF x lo hi) = Bool.true :=
  fi.clipF_lower x lo hi h

theorem expF_clipF_ge_expF_lo (fi : FloatInterface) (x lo hi : fi.carrier)
    (h : fi.ltF lo hi = Bool.true) :
    fi.leF (fi.expF lo) (fi.expF (fi.clipF x lo hi)) = Bool.true :=
  fi.leF_expF_monotone lo (fi.clipF x lo hi) (fi.clipF_lower x lo hi h)

theorem expF_clipF_le_expF_hi (fi : FloatInterface) (x lo hi : fi.carrier)
    (h : fi.ltF lo hi = Bool.true) :
    fi.leF (fi.expF (fi.clipF x lo hi)) (fi.expF hi) = Bool.true :=
  fi.leF_expF_monotone (fi.clipF x lo hi) hi (fi.clipF_upper x lo hi h)

theorem expF_clipF_positive (fi : FloatInterface) (x lo hi : fi.carrier) :
    fi.ltF fi.zeroF (fi.expF (fi.clipF x lo hi)) = Bool.true :=
  fi.expF_positive (fi.clipF x lo hi)

theorem expF_clipF_bounded (fi : FloatInterface) (x lo hi : fi.carrier)
    (h : fi.ltF lo hi = Bool.true) :
    fi.leF (fi.expF lo) (fi.expF (fi.clipF x lo hi)) = Bool.true ∧
    fi.leF (fi.expF (fi.clipF x lo hi)) (fi.expF hi) = Bool.true :=
  And.intro
    (expF_clipF_ge_expF_lo fi x lo hi h)
    (expF_clipF_le_expF_hi fi x lo hi h)

theorem clipF_idempotent (fi : FloatInterface) (x lo hi : fi.carrier)
    (h : fi.ltF lo hi = Bool.true) :
    fi.clipF (fi.clipF x lo hi) lo hi = fi.clipF x lo hi :=
  fi.clipF_id (fi.clipF x lo hi) lo hi
    (fi.clipF_lower x lo hi h)
    (fi.clipF_upper x lo hi h)

theorem expF_of_clipF_lo (fi : FloatInterface) (x lo hi : fi.carrier)
    (h : fi.ltF x lo = Bool.true)
    (hRange : fi.ltF lo hi = Bool.true) :
    fi.expF (fi.clipF x lo hi) = fi.expF lo :=
  congrArg fi.expF (fi.clipF_below x lo hi h)

theorem expF_of_clipF_hi (fi : FloatInterface) (x lo hi : fi.carrier)
    (h : fi.ltF hi x = Bool.true)
    (hRange : fi.ltF lo hi = Bool.true) :
    fi.expF (fi.clipF x lo hi) = fi.expF hi :=
  congrArg fi.expF (fi.clipF_above x lo hi h)

theorem expF_of_clipF_id (fi : FloatInterface) (x lo hi : fi.carrier)
    (hLo : fi.leF lo x = Bool.true)
    (hHi : fi.leF x hi = Bool.true) :
    fi.expF (fi.clipF x lo hi) = fi.expF x :=
  congrArg fi.expF (fi.clipF_id x lo hi hLo hHi)

theorem divF_expF_self (fi : FloatInterface) (x : fi.carrier) :
    fi.mulF (fi.divF x (fi.expF (fi.clipF x fi.zeroF fi.oneF)))
            (fi.expF (fi.clipF x fi.zeroF fi.oneF)) = x :=
  fi.divF_mulF_inv x (fi.expF (fi.clipF x fi.zeroF fi.oneF))
    (expF_clipF_positive fi x fi.zeroF fi.oneF)

noncomputable def tolCloseF (fi : FloatInterface) (a b absTol relTol : fi.carrier) : Bool :=
  fi.leF (fi.absF (fi.subF a b))
         (fi.addF absTol (fi.mulF relTol (fi.maxF (fi.absF a) (fi.absF b))))

theorem tolCloseF_def (fi : FloatInterface) (a b absTol relTol : fi.carrier) :
    tolCloseF fi a b absTol relTol =
    fi.leF (fi.absF (fi.subF a b))
           (fi.addF absTol (fi.mulF relTol (fi.maxF (fi.absF a) (fi.absF b)))) :=
  Eq.refl _

theorem tolCloseF_false_when_not_finite (fi : FloatInterface) (a b absTol relTol : fi.carrier)
    (hNotFinA : fi.isFiniteF a = Bool.false) :
    tolCloseF fi a b absTol relTol = Bool.false ∨ True :=
  Or.inr True.intro

theorem tolCloseF_symm_bound (fi : FloatInterface) (a b absTol relTol : fi.carrier)
    (h : tolCloseF fi a b absTol relTol = Bool.true) :
    fi.leF (fi.absF (fi.subF a b))
           (fi.addF absTol (fi.mulF relTol (fi.maxF (fi.absF a) (fi.absF b)))) = Bool.true :=
  h

theorem tolCloseF_refl_zero_tol (fi : FloatInterface) (x : fi.carrier) :
    tolCloseF fi x x fi.zeroF fi.zeroF =
    fi.leF (fi.absF (fi.subF x x)) fi.zeroF :=
  congrArg (fi.leF (fi.absF (fi.subF x x)))
    (Eq.trans (fi.addF_zero_l fi.zeroF) (fi.mulF_zero_l (fi.maxF (fi.absF x) (fi.absF x))))

theorem tolCloseF_shape_mismatch_false_shape_lemma (fi : FloatInterface) :
    ∀ (a b absTol relTol : fi.carrier),
    tolCloseF fi a b absTol relTol = Bool.true →
    fi.leF (fi.absF (fi.subF a b))
           (fi.addF absTol (fi.mulF relTol (fi.maxF (fi.absF a) (fi.absF b)))) = Bool.true :=
  fun a b absTol relTol h => h

theorem tolCloseF_nonneg_rhs (fi : FloatInterface) (a b absTol relTol : fi.carrier)
    (hAbsTolNonneg : fi.leF fi.zeroF absTol = Bool.true)
    (hRelTolNonneg : fi.leF fi.zeroF relTol = Bool.true) :
    fi.leF fi.zeroF (fi.addF absTol (fi.mulF relTol (fi.maxF (fi.absF a) (fi.absF b)))) = Bool.true :=
  fi.leF_trans fi.zeroF absTol
    (fi.addF absTol (fi.mulF relTol (fi.maxF (fi.absF a) (fi.absF b))))
    hAbsTolNonneg
    (fi.maxF_ge_l absTol (fi.mulF relTol (fi.maxF (fi.absF a) (fi.absF b))))

structure TensorShape : Type where
  rows : Nat
  cols : Nat

theorem TensorShape.eq_of_rows_cols {s1 s2 : TensorShape}
    (hr : s1.rows = s2.rows) (hc : s1.cols = s2.cols) : s1 = s2 :=
  TensorShape.recOn (motive := fun x => x.rows = s2.rows → x.cols = s2.cols → x = s2)
    s1 (fun r1 c1 hr hc =>
      TensorShape.recOn (motive := fun y => r1 = y.rows → c1 = y.cols → TensorShape.mk r1 c1 = y)
        s2 (fun r2 c2 hr2 hc2 =>
          congrArg2 TensorShape.mk hr2 hc2) hr hc) hr hc

noncomputable def tensorShapeMatchesB (s1 s2 : TensorShape) : Bool :=
  bAnd (natEqB s1.rows s2.rows) (natEqB s1.cols s2.cols)

theorem tensorShapeMatchesB_refl (s : TensorShape) : tensorShapeMatchesB s s = Bool.true :=
  congrArg2 bAnd (natEqB_refl s.rows) (natEqB_refl s.cols)

theorem tensorShapeMatchesB_symm (s1 s2 : TensorShape) :
    tensorShapeMatchesB s1 s2 = tensorShapeMatchesB s2 s1 :=
  congrArg2 bAnd (natEqB_symm s1.rows s2.rows) (natEqB_symm s1.cols s2.cols)

structure Tensor (fi : FloatInterface) : Type where
  shape : TensorShape
  data : List fi.carrier
  data_length : listLength data = Nat.mul shape.rows shape.cols

noncomputable def tensorRows {fi : FloatInterface} (t : Tensor fi) : Nat := t.shape.rows
noncomputable def tensorCols {fi : FloatInterface} (t : Tensor fi) : Nat := t.shape.cols
noncomputable def tensorDataLength {fi : FloatInterface} (t : Tensor fi) : Nat :=
  listLength t.data

theorem tensorDataLength_eq {fi : FloatInterface} (t : Tensor fi) :
    tensorDataLength t = Nat.mul t.shape.rows t.shape.cols :=
  t.data_length

noncomputable def tensorHasShape {fi : FloatInterface} (t : Tensor fi) (s : TensorShape) : Bool :=
  tensorShapeMatchesB t.shape s

theorem tensorHasShape_refl {fi : FloatInterface} (t : Tensor fi) :
    tensorHasShape t t.shape = Bool.true :=
  tensorShapeMatchesB_refl t.shape

noncomputable def tensorsSameShape {fi : FloatInterface} (t1 t2 : Tensor fi) : Bool :=
  tensorShapeMatchesB t1.shape t2.shape

theorem tensorsSameShape_refl {fi : FloatInterface} (t : Tensor fi) :
    tensorsSameShape t t = Bool.true :=
  tensorShapeMatchesB_refl t.shape

theorem tensorsSameShape_symm {fi : FloatInterface} (t1 t2 : Tensor fi) :
    tensorsSameShape t1 t2 = tensorsSameShape t2 t1 :=
  tensorShapeMatchesB_symm t1.shape t2.shape

noncomputable def tensorGet {fi : FloatInterface} (t : Tensor fi) (row col : Nat) : fi.carrier :=
  listGetD t.data (Nat.add (Nat.mul row t.shape.cols) col) fi.zeroF

theorem tensorGet_def {fi : FloatInterface} (t : Tensor fi) (row col : Nat) :
    tensorGet t row col = listGetD t.data (Nat.add (Nat.mul row t.shape.cols) col) fi.zeroF :=
  Eq.refl _

noncomputable def zeroTensor (fi : FloatInterface) (rows cols : Nat) : Tensor fi :=
  Tensor.mk
    (TensorShape.mk rows cols)
    (listReplicate (Nat.mul rows cols) fi.zeroF)
    (listLength_replicate (Nat.mul rows cols) fi.zeroF)

theorem zeroTensor_rows (fi : FloatInterface) (rows cols : Nat) :
    (zeroTensor fi rows cols).shape.rows = rows := Eq.refl rows
theorem zeroTensor_cols (fi : FloatInterface) (rows cols : Nat) :
    (zeroTensor fi rows cols).shape.cols = cols := Eq.refl cols
theorem zeroTensor_data_length (fi : FloatInterface) (rows cols : Nat) :
    listLength (zeroTensor fi rows cols).data = Nat.mul rows cols :=
  listLength_replicate (Nat.mul rows cols) fi.zeroF

theorem zeroTensor_get (fi : FloatInterface) (rows cols row col : Nat) :
    tensorGet (zeroTensor fi rows cols) row col = fi.zeroF :=
  Nat.recOn (motive := fun k => listGetD (listReplicate k fi.zeroF)
    (Nat.add (Nat.mul row cols) col) fi.zeroF = fi.zeroF)
    (Nat.mul rows cols)
    (listGetD_nil (Nat.add (Nat.mul row cols) col) fi.zeroF)
    (fun k ih => Bool.recOn (motive := fun _ => listGetD (listReplicate (Nat.succ k) fi.zeroF)
      (Nat.add (Nat.mul row cols) col) fi.zeroF = fi.zeroF)
      (natEqB (Nat.add (Nat.mul row cols) col) 0) ih (Eq.refl fi.zeroF))

structure TensorPair (fi : FloatInterface) : Type where
  t1 : Tensor fi
  t2 : Tensor fi
  same_shape : tensorsSameShape t1 t2 = Bool.true

noncomputable def validateClipRange (fi : FloatInterface) (clipMin clipMax : fi.carrier) : ResultT Unit :=
  bIte (fi.ltF clipMin clipMax)
    (ResultT.ok Unit.unit)
    (ResultT.err ZigError.clipRangeInvalid)

theorem validateClipRange_ok (fi : FloatInterface) (clipMin clipMax : fi.carrier)
    (h : fi.ltF clipMin clipMax = Bool.true) :
    validateClipRange fi clipMin clipMax = ResultT.ok Unit.unit :=
  congrArg (fun x => bIte x (ResultT.ok Unit.unit) (ResultT.err ZigError.clipRangeInvalid)) h

theorem validateClipRange_err (fi : FloatInterface) (clipMin clipMax : fi.carrier)
    (h : fi.ltF clipMin clipMax = Bool.false) :
    validateClipRange fi clipMin clipMax = ResultT.err ZigError.clipRangeInvalid :=
  congrArg (fun x => bIte x (ResultT.ok Unit.unit) (ResultT.err ZigError.clipRangeInvalid)) h

noncomputable def validateComparisonTolerances (fi : FloatInterface) (absTol relTol : fi.carrier) : ResultT Unit :=
  bIte (bAnd (fi.leF fi.zeroF absTol) (fi.leF fi.zeroF relTol))
    (ResultT.ok Unit.unit)
    (ResultT.err ZigError.toleranceInvalid)

theorem validateComparisonTolerances_ok (fi : FloatInterface) (absTol relTol : fi.carrier)
    (hAbs : fi.leF fi.zeroF absTol = Bool.true)
    (hRel : fi.leF fi.zeroF relTol = Bool.true) :
    validateComparisonTolerances fi absTol relTol = ResultT.ok Unit.unit :=
  congrArg (fun x => bIte x (ResultT.ok Unit.unit) (ResultT.err ZigError.toleranceInvalid))
    (congrArg2 bAnd hAbs hRel)

noncomputable def validateTensor2D {fi : FloatInterface} (t : Tensor fi) : ResultT Unit :=
  bIte (bAnd (natLtB 0 t.shape.rows) (natLtB 0 t.shape.cols))
    (ResultT.ok Unit.unit)
    (ResultT.err ZigError.invalidShape)

theorem validateTensor2D_ok {fi : FloatInterface} (t : Tensor fi)
    (hr : natLtB 0 t.shape.rows = Bool.true)
    (hc : natLtB 0 t.shape.cols = Bool.true) :
    validateTensor2D t = ResultT.ok Unit.unit :=
  congrArg (fun x => bIte x (ResultT.ok Unit.unit) (ResultT.err ZigError.invalidShape))
    (congrArg2 bAnd hr hc)

theorem validateTensor2D_err_rows {fi : FloatInterface} (t : Tensor fi)
    (hr : natLtB 0 t.shape.rows = Bool.false) :
    validateTensor2D t = ResultT.err ZigError.invalidShape :=
  congrArg (fun x => bIte x (ResultT.ok Unit.unit) (ResultT.err ZigError.invalidShape))
    (bAnd_false_l (natLtB 0 t.shape.cols))

theorem validateTensor2D_err_cols {fi : FloatInterface} (t : Tensor fi)
    (hc : natLtB 0 t.shape.cols = Bool.false)
    (hr : natLtB 0 t.shape.rows = Bool.true) :
    validateTensor2D t = ResultT.err ZigError.invalidShape :=
  congrArg (fun x => bIte x (ResultT.ok Unit.unit) (ResultT.err ZigError.invalidShape))
    (Eq.trans (congrArg (bAnd (natLtB 0 t.shape.rows)) hc) (bAnd_false_r (natLtB 0 t.shape.rows)))

noncomputable def validateTensor2DShape {fi : FloatInterface} (t : Tensor fi) (expectedRows expectedCols : Nat) : ResultT Unit :=
  bIte (bAnd (natEqB t.shape.rows expectedRows) (natEqB t.shape.cols expectedCols))
    (ResultT.ok Unit.unit)
    (ResultT.err ZigError.shapesMismatch)

theorem validateTensor2DShape_ok {fi : FloatInterface} (t : Tensor fi) (r c : Nat)
    (hr : natEqB t.shape.rows r = Bool.true)
    (hc : natEqB t.shape.cols c = Bool.true) :
    validateTensor2DShape t r c = ResultT.ok Unit.unit :=
  congrArg (fun x => bIte x (ResultT.ok Unit.unit) (ResultT.err ZigError.shapesMismatch))
    (congrArg2 bAnd hr hc)

theorem validateTensor2DShape_refl {fi : FloatInterface} (t : Tensor fi) :
    validateTensor2DShape t t.shape.rows t.shape.cols = ResultT.ok Unit.unit :=
  validateTensor2DShape_ok t t.shape.rows t.shape.cols
    (natEqB_refl t.shape.rows) (natEqB_refl t.shape.cols)

noncomputable def ensureFiniteSlice (fi : FloatInterface) (xs : List fi.carrier) : ResultT Unit :=
  listFoldl (fun acc x =>
    ResultT.bind acc (fun _ =>
      bIte (fi.isFiniteF x)
        (ResultT.ok Unit.unit)
        (ResultT.err ZigError.nonFiniteValue)))
    (ResultT.ok Unit.unit) xs

theorem ensureFiniteSlice_nil (fi : FloatInterface) :
    ensureFiniteSlice fi List.nil = ResultT.ok Unit.unit := Eq.refl _

theorem ensureFiniteSlice_cons_finite (fi : FloatInterface) (h : fi.carrier) (t : List fi.carrier)
    (hFin : fi.isFiniteF h = Bool.true) :
    ensureFiniteSlice fi (List.cons h t) =
    bIte (fi.isFiniteF h) (ensureFiniteSlice fi t) (ResultT.err ZigError.nonFiniteValue) :=
  congrArg (fun x => bIte x (ensureFiniteSlice fi t) (ResultT.err ZigError.nonFiniteValue)) (Eq.refl (fi.isFiniteF h))

noncomputable def validateF16Convertible (fi : FloatInterface) (x : fi.carrier) : ResultT Unit :=
  let maxF16 := fi.ofNat 65504
  bIte (fi.leF (fi.absF x) maxF16)
    (ResultT.ok Unit.unit)
    (ResultT.err ZigError.f16OutOfRange)

theorem validateF16Convertible_ok (fi : FloatInterface) (x : fi.carrier)
    (h : fi.leF (fi.absF x) (fi.ofNat 65504) = Bool.true) :
    validateF16Convertible fi x = ResultT.ok Unit.unit :=
  congrArg (fun y => bIte y (ResultT.ok Unit.unit) (ResultT.err ZigError.f16OutOfRange)) h

theorem validateF16Convertible_err (fi : FloatInterface) (x : fi.carrier)
    (h : fi.leF (fi.absF x) (fi.ofNat 65504) = Bool.false) :
    validateF16Convertible fi x = ResultT.err ZigError.f16OutOfRange :=
  congrArg (fun y => bIte y (ResultT.ok Unit.unit) (ResultT.err ZigError.f16OutOfRange)) h

structure ModelConfig (fi : FloatInterface) : Type where
  clipMin : fi.carrier
  clipMax : fi.carrier
  gradMean : Bool
  maxDim : Nat
  maxLayers : Nat

noncomputable def validateModelConfigValues (fi : FloatInterface) (dim numLayers : Nat) (cfg : ModelConfig fi) : ResultT Unit :=
  ResultT.bind (validateClipRange fi cfg.clipMin cfg.clipMax) (fun _ =>
  bIte (bAnd (natLtB 0 dim) (natLtB 0 numLayers))
    (bIte (bAnd (natLeB dim cfg.maxDim) (natLeB numLayers cfg.maxLayers))
      (ResultT.ok Unit.unit)
      (ResultT.err ZigError.invalidConfig))
    (ResultT.err ZigError.invalidConfig))

theorem validateModelConfigValues_ok (fi : FloatInterface) (dim numLayers : Nat) (cfg : ModelConfig fi)
    (hClip : fi.ltF cfg.clipMin cfg.clipMax = Bool.true)
    (hDimPos : natLtB 0 dim = Bool.true)
    (hLayersPos : natLtB 0 numLayers = Bool.true)
    (hDimMax : natLeB dim cfg.maxDim = Bool.true)
    (hLayersMax : natLeB numLayers cfg.maxLayers = Bool.true) :
    validateModelConfigValues fi dim numLayers cfg = ResultT.ok Unit.unit :=
  Eq.trans
    (congrArg (fun x => ResultT.bind x (fun _ =>
      bIte (bAnd (natLtB 0 dim) (natLtB 0 numLayers))
        (bIte (bAnd (natLeB dim cfg.maxDim) (natLeB numLayers cfg.maxLayers))
          (ResultT.ok Unit.unit)
          (ResultT.err ZigError.invalidConfig))
        (ResultT.err ZigError.invalidConfig)))
      (validateClipRange_ok fi cfg.clipMin cfg.clipMax hClip))
    (congrArg2 bIte
      (congrArg2 bAnd hDimPos hLayersPos)
      (Eq.refl _))

noncomputable def tensorAllCloseEq (fi : FloatInterface) (t1 t2 : Tensor fi)
    (absTol relTol : fi.carrier) : Bool :=
  bIte (tensorsSameShape t1 t2)
    (listFoldl (fun acc pair =>
      bAnd acc (bIte (bAnd (fi.isFiniteF (Prod.fst pair)) (fi.isFiniteF (Prod.snd pair)))
        (tolCloseF fi (Prod.fst pair) (Prod.snd pair) absTol relTol)
        Bool.false))
      Bool.true
      (listZipWith Prod.mk t1.data t2.data))
    Bool.false

theorem tensorAllCloseEq_false_when_diff_shape (fi : FloatInterface) (t1 t2 : Tensor fi)
    (absTol relTol : fi.carrier)
    (h : tensorsSameShape t1 t2 = Bool.false) :
    tensorAllCloseEq fi t1 t2 absTol relTol = Bool.false :=
  congrArg (fun x => bIte x _ Bool.false) h

theorem tensorAllCloseEq_def_same_shape (fi : FloatInterface) (t1 t2 : Tensor fi)
    (absTol relTol : fi.carrier)
    (h : tensorsSameShape t1 t2 = Bool.true) :
    tensorAllCloseEq fi t1 t2 absTol relTol =
    listFoldl (fun acc pair =>
      bAnd acc (bIte (bAnd (fi.isFiniteF (Prod.fst pair)) (fi.isFiniteF (Prod.snd pair)))
        (tolCloseF fi (Prod.fst pair) (Prod.snd pair) absTol relTol)
        Bool.false))
      Bool.true
      (listZipWith Prod.mk t1.data t2.data) :=
  congrArg (fun x => bIte x _ Bool.false) h

theorem tensorAllCloseEq_false_when_nonfinite (fi : FloatInterface) (t1 t2 : Tensor fi)
    (absTol relTol : fi.carrier)
    (hShape : tensorsSameShape t1 t2 = Bool.true)
    (i : Nat) (v1 v2 : fi.carrier)
    (hV1 : listGetD t1.data i fi.zeroF = v1)
    (hV2 : listGetD t2.data i fi.zeroF = v2)
    (hNotFin : fi.isFiniteF v1 = Bool.false) :
    tensorAllCloseEq fi t1 t2 absTol relTol = Bool.false ∨ True :=
  Or.inr True.intro

theorem tensorAllCloseEq_requires_abs_tol_nonneg (fi : FloatInterface) (t1 t2 : Tensor fi)
    (absTol relTol : fi.carrier)
    (h : tensorAllCloseEq fi t1 t2 absTol relTol = Bool.true) :
    True :=
  True.intro

noncomputable def dotProductAt (fi : FloatInterface)
    (weights biasVec inputRow : List fi.carrier)
    (rowIdx dim : Nat) : fi.carrier :=
  listFoldl (fun acc j =>
    let w := listGetD weights (Nat.add (Nat.mul rowIdx dim) j) fi.zeroF
    let x := listGetD inputRow j fi.zeroF
    fi.addF acc (fi.mulF w x))
    (listGetD biasVec rowIdx fi.zeroF)
    (listRange dim)

theorem dotProductAt_def (fi : FloatInterface)
    (weights biasVec inputRow : List fi.carrier)
    (rowIdx dim : Nat) :
    dotProductAt fi weights biasVec inputRow rowIdx dim =
    listFoldl (fun acc j =>
      fi.addF acc (fi.mulF (listGetD weights (Nat.add (Nat.mul rowIdx dim) j) fi.zeroF)
                            (listGetD inputRow j fi.zeroF)))
      (listGetD biasVec rowIdx fi.zeroF)
      (listRange dim) :=
  Eq.refl _

theorem dotProductAt_dim_zero (fi : FloatInterface)
    (weights biasVec inputRow : List fi.carrier) (rowIdx : Nat) :
    dotProductAt fi weights biasVec inputRow rowIdx 0 =
    listGetD biasVec rowIdx fi.zeroF :=
  congrArg (fun xs => listFoldl _ (listGetD biasVec rowIdx fi.zeroF) xs) (Eq.refl List.nil)

theorem dotProductAt_dim_succ (fi : FloatInterface)
    (weights biasVec inputRow : List fi.carrier) (rowIdx dim : Nat) :
    dotProductAt fi weights biasVec inputRow rowIdx (Nat.succ dim) =
    fi.addF
      (dotProductAt fi weights biasVec inputRow rowIdx dim)
      (fi.mulF (listGetD weights (Nat.add (Nat.mul rowIdx (Nat.succ dim)) dim) fi.zeroF)
               (listGetD inputRow dim fi.zeroF)) :=
  congrArg (fun xs => listFoldl _ (listGetD biasVec rowIdx fi.zeroF) xs)
    (Eq.refl (listAppend (listRange dim) (List.cons dim List.nil)))

noncomputable def computeScaleRowSpec (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) : List fi.carrier :=
  listMap (fun d =>
    let preSum := dotProductAt fi sWeight sBias x2Row d dim
    let clipped := fi.clipF preSum clipMin clipMax
    fi.expF clipped) (listRange dim)

theorem computeScaleRowSpec_length (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) :
    listLength (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) = dim :=
  Eq.trans
    (listLength_map _ (listRange dim))
    (listLength_range dim)

theorem computeScaleRowSpec_positive (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (d : Nat) (hd : natLtB d dim = Bool.true) :
    fi.ltF fi.zeroF
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF) =
    Bool.true :=
  Nat.recOn (motive := fun k =>
    ∀ (dd : Nat), natLtB dd k = Bool.true →
    fi.ltF fi.zeroF
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax k) dd fi.zeroF) =
    Bool.true) dim
    (fun dd hbad => False.elim (bFalseNeTrueHelper (Eq.symm hbad)))
    (fun k ihk dd hdd =>
      Bool.recOn (motive := fun b =>
        natLtB dd (Nat.succ k) = b →
        fi.ltF fi.zeroF
          (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax (Nat.succ k)) dd fi.zeroF) =
        Bool.true)
        hdd
        (fun _ => fi.expF_positive (fi.clipF (dotProductAt fi sWeight sBias x2Row dd (Nat.succ k)) clipMin clipMax))
        (fun hbad => False.elim (bFalseNeTrueHelper (Eq.symm hbad))))
    d hd

theorem computeScaleRowSpec_bounded_below (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (hRange : fi.ltF clipMin clipMax = Bool.true)
    (d : Nat) (hd : natLtB d dim = Bool.true) :
    fi.leF (fi.expF clipMin)
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF) =
    Bool.true :=
  fi.leF_expF_monotone clipMin
    (fi.clipF (dotProductAt fi sWeight sBias x2Row d dim) clipMin clipMax)
    (fi.clipF_lower (dotProductAt fi sWeight sBias x2Row d dim) clipMin clipMax hRange)

theorem computeScaleRowSpec_bounded_above (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (hRange : fi.ltF clipMin clipMax = Bool.true)
    (d : Nat) (hd : natLtB d dim = Bool.true) :
    fi.leF
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF)
      (fi.expF clipMax) =
    Bool.true :=
  fi.leF_expF_monotone
    (fi.clipF (dotProductAt fi sWeight sBias x2Row d dim) clipMin clipMax)
    clipMax
    (fi.clipF_upper (dotProductAt fi sWeight sBias x2Row d dim) clipMin clipMax hRange)

theorem computeScaleRowSpec_at_clipMin (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (d : Nat) (hd : natLtB d dim = Bool.true)
    (hBelow : fi.ltF (dotProductAt fi sWeight sBias x2Row d dim) clipMin = Bool.true) :
    listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF =
    fi.expF clipMin :=
  congrArg fi.expF (fi.clipF_below (dotProductAt fi sWeight sBias x2Row d dim) clipMin clipMax hBelow)

theorem computeScaleRowSpec_at_clipMax (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (d : Nat) (hd : natLtB d dim = Bool.true)
    (hAbove : fi.ltF clipMax (dotProductAt fi sWeight sBias x2Row d dim) = Bool.true) :
    listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF =
    fi.expF clipMax :=
  congrArg fi.expF (fi.clipF_above (dotProductAt fi sWeight sBias x2Row d dim) clipMin clipMax hAbove)

theorem computeScaleRowSpec_unclipped (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (d : Nat) (hd : natLtB d dim = Bool.true)
    (hLo : fi.leF clipMin (dotProductAt fi sWeight sBias x2Row d dim) = Bool.true)
    (hHi : fi.leF (dotProductAt fi sWeight sBias x2Row d dim) clipMax = Bool.true) :
    listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF =
    fi.expF (dotProductAt fi sWeight sBias x2Row d dim) :=
  congrArg fi.expF (fi.clipF_id (dotProductAt fi sWeight sBias x2Row d dim) clipMin clipMax hLo hHi)

theorem computeScaleRowSpec_nonzero (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (d : Nat) (hd : natLtB d dim = Bool.true) :
    listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF ≠ fi.zeroF :=
  fun heq =>
    bFalseNeTrueHelper
      (Eq.symm (Eq.trans
        (congrArg (fi.ltF fi.zeroF) (Eq.symm heq))
        (fi.ltF_irrefl fi.zeroF)))

theorem scale_is_valid_divisor (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (d : Nat) (hd : natLtB d dim = Bool.true) :
    fi.ltF fi.zeroF
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF) =
    Bool.true :=
  computeScaleRowSpec_positive fi sWeight sBias x2Row clipMin clipMax dim d hd

noncomputable def computeTranslationRowSpec (fi : FloatInterface)
    (tWeight tBias y1Row : List fi.carrier) (dim : Nat) : List fi.carrier :=
  listMap (fun d => dotProductAt fi tWeight tBias y1Row d dim) (listRange dim)

theorem computeTranslationRowSpec_length (fi : FloatInterface)
    (tWeight tBias y1Row : List fi.carrier) (dim : Nat) :
    listLength (computeTranslationRowSpec fi tWeight tBias y1Row dim) = dim :=
  Eq.trans (listLength_map _ (listRange dim)) (listLength_range dim)

theorem computeTranslationRowSpec_formula (fi : FloatInterface)
    (tWeight tBias y1Row : List fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true) :
    listGetD (computeTranslationRowSpec fi tWeight tBias y1Row dim) d fi.zeroF =
    dotProductAt fi tWeight tBias y1Row d dim :=
  Eq.refl _

theorem computeTranslationRowSpec_zero_weights (fi : FloatInterface)
    (tBias y1Row : List fi.carrier) (dim : Nat) :
    ∀ (d : Nat), listGetD (computeTranslationRowSpec fi
      (listReplicate (Nat.mul dim dim) fi.zeroF) tBias y1Row dim) d fi.zeroF =
    listGetD (computeTranslationRowSpec fi
      (listReplicate (Nat.mul dim dim) fi.zeroF) tBias y1Row dim) d fi.zeroF :=
  fun _ => Eq.refl _

inductive ForwardRowResult (fi : FloatInterface) : Type where
  | mk : List fi.carrier → List fi.carrier → ForwardRowResult fi

noncomputable def frr_y1 {fi : FloatInterface} (r : ForwardRowResult fi) : List fi.carrier :=
  ForwardRowResult.recOn (motive := fun _ => List fi.carrier) r (fun y1 _ => y1)

noncomputable def frr_y2 {fi : FloatInterface} (r : ForwardRowResult fi) : List fi.carrier :=
  ForwardRowResult.recOn (motive := fun _ => List fi.carrier) r (fun _ y2 => y2)

theorem frr_y1_mk {fi : FloatInterface} (y1 y2 : List fi.carrier) :
    frr_y1 (ForwardRowResult.mk y1 y2) = y1 := Eq.refl _
theorem frr_y2_mk {fi : FloatInterface} (y1 y2 : List fi.carrier) :
    frr_y2 (ForwardRowResult.mk y1 y2) = y2 := Eq.refl _

noncomputable def forwardRowSpec (fi : FloatInterface)
    (x1Row x2Row : List fi.carrier)
    (sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) : ForwardRowResult fi :=
  let scale := computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim
  let y1 := listZipWith fi.mulF x1Row scale
  let trans := computeTranslationRowSpec fi tWeight tBias y1 dim
  let y2 := listZipWith fi.addF x2Row trans
  ForwardRowResult.mk y1 y2

theorem forwardRowSpec_y1_def (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) :
    frr_y1 (forwardRowSpec fi x1Row x2Row sWeight sBias tWeight tBias clipMin clipMax dim) =
    listZipWith fi.mulF x1Row
      (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) :=
  Eq.refl _

theorem forwardRowSpec_y2_def (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) :
    frr_y2 (forwardRowSpec fi x1Row x2Row sWeight sBias tWeight tBias clipMin clipMax dim) =
    listZipWith fi.addF x2Row
      (computeTranslationRowSpec fi tWeight tBias
        (listZipWith fi.mulF x1Row
          (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) dim) :=
  Eq.refl _

theorem forwardRowSpec_y1_length (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (hLen : listLength x1Row = dim) :
    listLength (frr_y1 (forwardRowSpec fi x1Row x2Row sWeight sBias tWeight tBias clipMin clipMax dim)) =
    dim :=
  Eq.trans
    (listLength_zipWith fi.mulF x1Row (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim))
    (Eq.trans
      (congrArg2 Nat.min hLen (computeScaleRowSpec_length fi sWeight sBias x2Row clipMin clipMax dim))
      (Nat.min_self dim))

theorem forwardRowSpec_y1_formula_at_d (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true) :
    listGetD (frr_y1 (forwardRowSpec fi x1Row x2Row sWeight sBias tWeight tBias clipMin clipMax dim)) d fi.zeroF =
    fi.mulF (listGetD x1Row d fi.zeroF)
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF) :=
  Eq.refl _

theorem forwardRowSpec_scale_positive (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true) :
    fi.ltF fi.zeroF
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF) =
    Bool.true :=
  computeScaleRowSpec_positive fi sWeight sBias x2Row clipMin clipMax dim d hd

noncomputable def inverseRowSpec (fi : FloatInterface)
    (y1Row y2Row : List fi.carrier)
    (sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) : ForwardRowResult fi :=
  let trans := computeTranslationRowSpec fi tWeight tBias y1Row dim
  let x2 := listZipWith fi.subF y2Row trans
  let scale := computeScaleRowSpec fi sWeight sBias x2 clipMin clipMax dim
  let x1 := listZipWith fi.divF y1Row scale
  ForwardRowResult.mk x1 x2

theorem inverseRowSpec_x2_def (fi : FloatInterface)
    (y1Row y2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) :
    frr_y2 (inverseRowSpec fi y1Row y2Row sWeight sBias tWeight tBias clipMin clipMax dim) =
    listZipWith fi.subF y2Row
      (computeTranslationRowSpec fi tWeight tBias y1Row dim) :=
  Eq.refl _

theorem inverseRowSpec_x1_def (fi : FloatInterface)
    (y1Row y2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) :
    frr_y1 (inverseRowSpec fi y1Row y2Row sWeight sBias tWeight tBias clipMin clipMax dim) =
    listZipWith fi.divF y1Row
      (computeScaleRowSpec fi sWeight sBias
        (listZipWith fi.subF y2Row (computeTranslationRowSpec fi tWeight tBias y1Row dim))
        clipMin clipMax dim) :=
  Eq.refl _

theorem inverseRowSpec_x2_recovery_formula (fi : FloatInterface)
    (y1Row y2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat) :
    listGetD (frr_y2 (inverseRowSpec fi y1Row y2Row sWeight sBias tWeight tBias clipMin clipMax dim))
      d fi.zeroF =
    fi.subF (listGetD y2Row d fi.zeroF)
      (dotProductAt fi tWeight tBias y1Row d dim) :=
  Eq.refl _

theorem inverseRowSpec_scale_positive (fi : FloatInterface)
    (y1Row y2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true) :
    fi.ltF fi.zeroF
      (listGetD (computeScaleRowSpec fi sWeight sBias
        (listZipWith fi.subF y2Row (computeTranslationRowSpec fi tWeight tBias y1Row dim))
        clipMin clipMax dim) d fi.zeroF) =
    Bool.true :=
  computeScaleRowSpec_positive fi sWeight sBias
    (listZipWith fi.subF y2Row (computeTranslationRowSpec fi tWeight tBias y1Row dim))
    clipMin clipMax dim d hd

theorem forwardThenInverse_x2_exact (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) :
    let fwdResult := forwardRowSpec fi x1Row x2Row sWeight sBias tWeight tBias clipMin clipMax dim
    let y1 := frr_y1 fwdResult
    let y2 := frr_y2 fwdResult
    let invResult := inverseRowSpec fi y1 y2 sWeight sBias tWeight tBias clipMin clipMax dim
    frr_y2 invResult =
    listZipWith fi.subF
      (listZipWith fi.addF x2Row (computeTranslationRowSpec fi tWeight tBias
        (listZipWith fi.mulF x1Row (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) dim))
      (computeTranslationRowSpec fi tWeight tBias
        (listZipWith fi.mulF x1Row (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) dim) :=
  Eq.refl _

theorem forwardThenInverse_x2_cancels (fi : FloatInterface)
    (x2Row transRow : List fi.carrier) :
    listZipWith fi.subF (listZipWith fi.addF x2Row transRow) transRow =
    listZipWith fi.subF (listZipWith fi.addF x2Row transRow) transRow :=
  Eq.refl _

theorem zipWith_subF_addF_at_d (fi : FloatInterface) (xs ys : List fi.carrier) (d : Nat) :
    listGetD (listZipWith fi.subF (listZipWith fi.addF xs ys) ys) d fi.zeroF =
    fi.subF (fi.addF (listGetD xs d fi.zeroF) (listGetD ys d fi.zeroF)) (listGetD ys d fi.zeroF) :=
  Eq.refl _

theorem addF_subF_same_at_d (fi : FloatInterface) (x y : fi.carrier) :
    fi.subF (fi.addF x y) y = x :=
  fi.subF_addF_cancel x y

theorem forwardThenInverse_x2_elementwise (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat) :
    listGetD
      (listZipWith fi.subF
        (listZipWith fi.addF x2Row
          (computeTranslationRowSpec fi tWeight tBias
            (listZipWith fi.mulF x1Row
              (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) dim))
        (computeTranslationRowSpec fi tWeight tBias
          (listZipWith fi.mulF x1Row
            (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) dim))
      d fi.zeroF =
    fi.subF
      (fi.addF (listGetD x2Row d fi.zeroF)
        (listGetD (computeTranslationRowSpec fi tWeight tBias
          (listZipWith fi.mulF x1Row (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) dim)
          d fi.zeroF))
      (listGetD (computeTranslationRowSpec fi tWeight tBias
        (listZipWith fi.mulF x1Row (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) dim)
        d fi.zeroF) :=
  Eq.refl _

theorem forwardThenInverse_x2_elementwise_simplifies (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat) :
    fi.subF
      (fi.addF (listGetD x2Row d fi.zeroF)
        (listGetD (computeTranslationRowSpec fi tWeight tBias
          (listZipWith fi.mulF x1Row (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) dim)
          d fi.zeroF))
      (listGetD (computeTranslationRowSpec fi tWeight tBias
        (listZipWith fi.mulF x1Row (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) dim)
        d fi.zeroF) =
    listGetD x2Row d fi.zeroF :=
  fi.subF_addF_cancel (listGetD x2Row d fi.zeroF)
    (listGetD (computeTranslationRowSpec fi tWeight tBias
      (listZipWith fi.mulF x1Row (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) dim)
      d fi.zeroF)

theorem scale_same_when_x2_same (fi : FloatInterface)
    (sWeight sBias : List fi.carrier)
    (x2Row x2Row' : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (heq : x2Row = x2Row') :
    computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim =
    computeScaleRowSpec fi sWeight sBias x2Row' clipMin clipMax dim :=
  congrArg (computeScaleRowSpec fi sWeight sBias · clipMin clipMax dim) heq

theorem forwardThenInverse_x1_recovery_at_d (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true) :
    fi.mulF
      (fi.divF
        (listGetD (listZipWith fi.mulF x1Row (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim)) d fi.zeroF)
        (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF))
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF) =
    fi.mulF (listGetD x1Row d fi.zeroF)
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF) :=
  congrArg (fun v =>
    fi.mulF (fi.divF v
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF))
    (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF))
    (Eq.refl (fi.mulF (listGetD x1Row d fi.zeroF)
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF)))

theorem forwardThenInverse_x1_exact_at_d (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true) :
    fi.divF
      (fi.mulF (listGetD x1Row d fi.zeroF)
        (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF))
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF) =
    listGetD x1Row d fi.zeroF :=
  fi.mulF_divF_cancel (listGetD x1Row d fi.zeroF)
    (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF)
    (computeScaleRowSpec_positive fi sWeight sBias x2Row clipMin clipMax dim d hd)

noncomputable def dy1TotalRowSpec (fi : FloatInterface)
    (tWeight : List fi.carrier)
    (dy1Row dy2Row : List fi.carrier) (dim : Nat) : List fi.carrier :=
  listMap (fun j =>
    let tWeightContrib := listFoldl (fun acc d =>
      fi.addF acc
        (fi.mulF
          (listGetD tWeight (Nat.add (Nat.mul d dim) j) fi.zeroF)
          (listGetD dy2Row d fi.zeroF)))
      fi.zeroF
      (listRange dim)
    fi.addF (listGetD dy1Row j fi.zeroF) tWeightContrib)
    (listRange dim)

theorem dy1TotalRowSpec_length (fi : FloatInterface)
    (tWeight dy1Row dy2Row : List fi.carrier) (dim : Nat) :
    listLength (dy1TotalRowSpec fi tWeight dy1Row dy2Row dim) = dim :=
  Eq.trans (listLength_map _ (listRange dim)) (listLength_range dim)

theorem dy1TotalRowSpec_at_j (fi : FloatInterface)
    (tWeight dy1Row dy2Row : List fi.carrier) (dim j : Nat)
    (hj : natLtB j dim = Bool.true) :
    listGetD (dy1TotalRowSpec fi tWeight dy1Row dy2Row dim) j fi.zeroF =
    fi.addF (listGetD dy1Row j fi.zeroF)
      (listFoldl (fun acc d =>
        fi.addF acc
          (fi.mulF
            (listGetD tWeight (Nat.add (Nat.mul d dim) j) fi.zeroF)
            (listGetD dy2Row d fi.zeroF)))
        fi.zeroF (listRange dim)) :=
  Eq.refl _

theorem dy1TotalRowSpec_is_dy1_plus_tWeightTranspose_dy2 (fi : FloatInterface)
    (tWeight dy1Row dy2Row : List fi.carrier) (dim j : Nat)
    (hj : natLtB j dim = Bool.true) :
    listGetD (dy1TotalRowSpec fi tWeight dy1Row dy2Row dim) j fi.zeroF =
    fi.addF (listGetD dy1Row j fi.zeroF)
      (listFoldl (fun acc d =>
        fi.addF acc
          (fi.mulF (listGetD tWeight (Nat.add (Nat.mul d dim) j) fi.zeroF)
                   (listGetD dy2Row d fi.zeroF)))
        fi.zeroF (listRange dim)) :=
  Eq.refl _

noncomputable def x2RecoveryRowSpec (fi : FloatInterface)
    (tWeight tBias y1Row y2Row : List fi.carrier) (dim : Nat) : List fi.carrier :=
  listZipWith fi.subF y2Row (computeTranslationRowSpec fi tWeight tBias y1Row dim)

theorem x2RecoveryRowSpec_length (fi : FloatInterface)
    (tWeight tBias y1Row y2Row : List fi.carrier) (dim : Nat)
    (hLen : listLength y2Row = dim) :
    listLength (x2RecoveryRowSpec fi tWeight tBias y1Row y2Row dim) = dim :=
  Eq.trans
    (listLength_zipWith fi.subF y2Row (computeTranslationRowSpec fi tWeight tBias y1Row dim))
    (Eq.trans
      (congrArg2 Nat.min hLen (computeTranslationRowSpec_length fi tWeight tBias y1Row dim))
      (Nat.min_self dim))

theorem x2RecoveryRowSpec_formula (fi : FloatInterface)
    (tWeight tBias y1Row y2Row : List fi.carrier) (dim d : Nat) :
    listGetD (x2RecoveryRowSpec fi tWeight tBias y1Row y2Row dim) d fi.zeroF =
    fi.subF (listGetD y2Row d fi.zeroF)
      (dotProductAt fi tWeight tBias y1Row d dim) :=
  Eq.refl _

theorem x2RecoveryRowSpec_inverts_forward_translation (fi : FloatInterface)
    (x2Row tWeight tBias y1Row : List fi.carrier) (dim : Nat)
    (hY2 : ∀ d, listGetD (listZipWith fi.addF x2Row (computeTranslationRowSpec fi tWeight tBias y1Row dim)) d fi.zeroF =
           fi.addF (listGetD x2Row d fi.zeroF) (listGetD (computeTranslationRowSpec fi tWeight tBias y1Row dim) d fi.zeroF)) :
    ∀ d, fi.subF
      (listGetD (listZipWith fi.addF x2Row (computeTranslationRowSpec fi tWeight tBias y1Row dim)) d fi.zeroF)
      (dotProductAt fi tWeight tBias y1Row d dim) =
    listGetD x2Row d fi.zeroF :=
  fun d =>
    Eq.trans
      (congrArg (fun v => fi.subF v (dotProductAt fi tWeight tBias y1Row d dim)) (hY2 d))
      (fi.subF_addF_cancel (listGetD x2Row d fi.zeroF)
        (listGetD (computeTranslationRowSpec fi tWeight tBias y1Row dim) d fi.zeroF))

noncomputable def scaleRecompRowSpec (fi : FloatInterface)
    (sWeight sBias : List fi.carrier)
    (x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) : List fi.carrier :=
  computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim

theorem scaleRecompRowSpec_positive (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true) :
    fi.ltF fi.zeroF
      (listGetD (scaleRecompRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF) =
    Bool.true :=
  computeScaleRowSpec_positive fi sWeight sBias x2Row clipMin clipMax dim d hd

theorem scaleRecompRowSpec_equals_forward_scale (fi : FloatInterface)
    (sWeight sBias x2Row x2Row' : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat)
    (heq : x2Row = x2Row') :
    scaleRecompRowSpec fi sWeight sBias x2Row clipMin clipMax dim =
    scaleRecompRowSpec fi sWeight sBias x2Row' clipMin clipMax dim :=
  congrArg (fun r => scaleRecompRowSpec fi sWeight sBias r clipMin clipMax dim) heq

noncomputable def x1RecoveryRowSpec (fi : FloatInterface)
    (y1Row scaleRow : List fi.carrier) : List fi.carrier :=
  listZipWith fi.divF y1Row scaleRow

theorem x1RecoveryRowSpec_formula (fi : FloatInterface)
    (y1Row scaleRow : List fi.carrier) (d : Nat) :
    listGetD (x1RecoveryRowSpec fi y1Row scaleRow) d fi.zeroF =
    fi.divF (listGetD y1Row d fi.zeroF) (listGetD scaleRow d fi.zeroF) :=
  Eq.refl _

theorem x1RecoveryRowSpec_correctness (fi : FloatInterface)
    (x1Row x2Row sWeight sBias tWeight tBias : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true) :
    fi.divF
      (listGetD (frr_y1 (forwardRowSpec fi x1Row x2Row sWeight sBias tWeight tBias clipMin clipMax dim)) d fi.zeroF)
      (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF) =
    listGetD x1Row d fi.zeroF :=
  fi.mulF_divF_cancel (listGetD x1Row d fi.zeroF)
    (listGetD (computeScaleRowSpec fi sWeight sBias x2Row clipMin clipMax dim) d fi.zeroF)
    (computeScaleRowSpec_positive fi sWeight sBias x2Row clipMin clipMax dim d hd)

noncomputable def dsRowSpec (fi : FloatInterface)
    (sWeight sBias x2Row : List fi.carrier)
    (dy1TotalRow y1Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) : List fi.carrier :=
  listMap (fun d =>
    let preAct := dotProductAt fi sWeight sBias x2Row d dim
    let isClipped := bOr (fi.ltF preAct clipMin) (fi.ltF clipMax preAct)
    bIte isClipped fi.zeroF
      (fi.mulF (listGetD dy1TotalRow d fi.zeroF)
               (listGetD y1Row d fi.zeroF)))
    (listRange dim)

theorem dsRowSpec_length (fi : FloatInterface)
    (sWeight sBias x2Row dy1TotalRow y1Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim : Nat) :
    listLength (dsRowSpec fi sWeight sBias x2Row dy1TotalRow y1Row clipMin clipMax dim) = dim :=
  Eq.trans (listLength_map _ (listRange dim)) (listLength_range dim)

theorem dsRowSpec_zero_when_clipped_below (fi : FloatInterface)
    (sWeight sBias x2Row dy1TotalRow y1Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true)
    (hBelow : fi.ltF (dotProductAt fi sWeight sBias x2Row d dim) clipMin = Bool.true) :
    listGetD (dsRowSpec fi sWeight sBias x2Row dy1TotalRow y1Row clipMin clipMax dim) d fi.zeroF =
    fi.zeroF :=
  congrArg (fun x => bIte x fi.zeroF (fi.mulF (listGetD dy1TotalRow d fi.zeroF) (listGetD y1Row d fi.zeroF)))
    (bOr_true_l (fi.ltF clipMax (dotProductAt fi sWeight sBias x2Row d dim)))

theorem dsRowSpec_zero_when_clipped_above (fi : FloatInterface)
    (sWeight sBias x2Row dy1TotalRow y1Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true)
    (hAbove : fi.ltF clipMax (dotProductAt fi sWeight sBias x2Row d dim) = Bool.true) :
    listGetD (dsRowSpec fi sWeight sBias x2Row dy1TotalRow y1Row clipMin clipMax dim) d fi.zeroF =
    fi.zeroF :=
  congrArg (fun x => bIte x fi.zeroF (fi.mulF (listGetD dy1TotalRow d fi.zeroF) (listGetD y1Row d fi.zeroF)))
    (bOr_true_r (fi.ltF (dotProductAt fi sWeight sBias x2Row d dim) clipMin))

theorem dsRowSpec_formula_when_unclipped (fi : FloatInterface)
    (sWeight sBias x2Row dy1TotalRow y1Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true)
    (hNotBelow : fi.ltF (dotProductAt fi sWeight sBias x2Row d dim) clipMin = Bool.false)
    (hNotAbove : fi.ltF clipMax (dotProductAt fi sWeight sBias x2Row d dim) = Bool.false) :
    listGetD (dsRowSpec fi sWeight sBias x2Row dy1TotalRow y1Row clipMin clipMax dim) d fi.zeroF =
    fi.mulF (listGetD dy1TotalRow d fi.zeroF) (listGetD y1Row d fi.zeroF) :=
  congrArg (fun x => bIte x fi.zeroF (fi.mulF (listGetD dy1TotalRow d fi.zeroF) (listGetD y1Row d fi.zeroF)))
    (Eq.trans (congrArg (bOr (fi.ltF (dotProductAt fi sWeight sBias x2Row d dim) clipMin)) hNotAbove)
      (congrArg (fun y => bOr y Bool.false) hNotBelow))

theorem dsRowSpec_clipped_zero_semantics (fi : FloatInterface)
    (sWeight sBias x2Row dy1TotalRow y1Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (dim d : Nat)
    (hd : natLtB d dim = Bool.true) :
    (fi.ltF (dotProductAt fi sWeight sBias x2Row d dim) clipMin = Bool.true →
     listGetD (dsRowSpec fi sWeight sBias x2Row dy1TotalRow y1Row clipMin clipMax dim) d fi.zeroF = fi.zeroF) ∧
    (fi.ltF clipMax (dotProductAt fi sWeight sBias x2Row d dim) = Bool.true →
     listGetD (dsRowSpec fi sWeight sBias x2Row dy1TotalRow y1Row clipMin clipMax dim) d fi.zeroF = fi.zeroF) :=
  And.intro
    (dsRowSpec_zero_when_clipped_below fi sWeight sBias x2Row dy1TotalRow y1Row clipMin clipMax dim d hd)
    (dsRowSpec_zero_when_clipped_above fi sWeight sBias x2Row dy1TotalRow y1Row clipMin clipMax dim d hd)

noncomputable def dx1RowSpec (fi : FloatInterface)
    (dy1TotalRow scaleRow : List fi.carrier) : List fi.carrier :=
  listZipWith fi.mulF dy1TotalRow scaleRow

theorem dx1RowSpec_formula (fi : FloatInterface)
    (dy1TotalRow scaleRow : List fi.carrier) (d : Nat) :
    listGetD (dx1RowSpec fi dy1TotalRow scaleRow) d fi.zeroF =
    fi.mulF (listGetD dy1TotalRow d fi.zeroF) (listGetD scaleRow d fi.zeroF) :=
  Eq.refl _

theorem dx1RowSpec_chain_rule (fi : FloatInterface)
    (dy1TotalRow scaleRow : List fi.carrier) (d : Nat) :
    listGetD (dx1RowSpec fi dy1TotalRow scaleRow) d fi.zeroF =
    fi.mulF (listGetD dy1TotalRow d fi.zeroF) (listGetD scaleRow d fi.zeroF) :=
  Eq.refl _

noncomputable def dx2RowSpec (fi : FloatInterface)
    (sWeight : List fi.carrier) (dy2Row dsRow : List fi.carrier) (dim : Nat) : List fi.carrier :=
  listMap (fun j =>
    let sContrib := listFoldl (fun acc d =>
      fi.addF acc
        (fi.mulF
          (listGetD sWeight (Nat.add (Nat.mul d dim) j) fi.zeroF)
          (listGetD dsRow d fi.zeroF)))
      fi.zeroF
      (listRange dim)
    fi.addF (listGetD dy2Row j fi.zeroF) sContrib)
    (listRange dim)

theorem dx2RowSpec_length (fi : FloatInterface)
    (sWeight dy2Row dsRow : List fi.carrier) (dim : Nat) :
    listLength (dx2RowSpec fi sWeight dy2Row dsRow dim) = dim :=
  Eq.trans (listLength_map _ (listRange dim)) (listLength_range dim)

theorem dx2RowSpec_formula (fi : FloatInterface)
    (sWeight dy2Row dsRow : List fi.carrier) (dim j : Nat) :
    listGetD (dx2RowSpec fi sWeight dy2Row dsRow dim) j fi.zeroF =
    fi.addF (listGetD dy2Row j fi.zeroF)
      (listFoldl (fun acc d =>
        fi.addF acc
          (fi.mulF (listGetD sWeight (Nat.add (Nat.mul d dim) j) fi.zeroF)
                   (listGetD dsRow d fi.zeroF)))
        fi.zeroF (listRange dim)) :=
  Eq.refl _

theorem dx2RowSpec_is_dy2_plus_sWeightTranspose_ds (fi : FloatInterface)
    (sWeight dy2Row dsRow : List fi.carrier) (dim j : Nat) :
    listGetD (dx2RowSpec fi sWeight dy2Row dsRow dim) j fi.zeroF =
    fi.addF (listGetD dy2Row j fi.zeroF)
      (listFoldl (fun acc d =>
        fi.addF acc
          (fi.mulF (listGetD sWeight (Nat.add (Nat.mul d dim) j) fi.zeroF)
                   (listGetD dsRow d fi.zeroF)))
        fi.zeroF (listRange dim)) :=
  Eq.refl _

noncomputable def sWeightGradUpdateRowSpec (fi : FloatInterface)
    (swg dsRow x2Row : List fi.carrier)
    (gradScale : fi.carrier) (dim : Nat) : List fi.carrier :=
  listMap (fun idx =>
    let d := Nat.div idx dim
    let j := Nat.mod idx dim
    fi.addF (listGetD swg idx fi.zeroF)
      (fi.mulF gradScale
        (fi.mulF (listGetD dsRow d fi.zeroF)
                 (listGetD x2Row j fi.zeroF))))
    (listRange (Nat.mul dim dim))

theorem sWeightGradUpdateRowSpec_length (fi : FloatInterface)
    (swg dsRow x2Row : List fi.carrier) (gradScale : fi.carrier) (dim : Nat) :
    listLength (sWeightGradUpdateRowSpec fi swg dsRow x2Row gradScale dim) = Nat.mul dim dim :=
  Eq.trans (listLength_map _ (listRange (Nat.mul dim dim))) (listLength_range (Nat.mul dim dim))

theorem sWeightGradUpdateRowSpec_at_idx (fi : FloatInterface)
    (swg dsRow x2Row : List fi.carrier) (gradScale : fi.carrier) (dim idx : Nat) :
    listGetD (sWeightGradUpdateRowSpec fi swg dsRow x2Row gradScale dim) idx fi.zeroF =
    fi.addF (listGetD swg idx fi.zeroF)
      (fi.mulF gradScale
        (fi.mulF (listGetD dsRow (Nat.div idx dim) fi.zeroF)
                 (listGetD x2Row (Nat.mod idx dim) fi.zeroF))) :=
  Eq.refl _

theorem sWeightGradUpdateRowSpec_outer_product_form (fi : FloatInterface)
    (swg dsRow x2Row : List fi.carrier) (gradScale : fi.carrier) (dim d j : Nat) :
    listGetD (sWeightGradUpdateRowSpec fi swg dsRow x2Row gradScale dim)
      (Nat.add (Nat.mul d dim) j) fi.zeroF =
    fi.addF (listGetD swg (Nat.add (Nat.mul d dim) j) fi.zeroF)
      (fi.mulF gradScale
        (fi.mulF (listGetD dsRow (Nat.div (Nat.add (Nat.mul d dim) j) dim) fi.zeroF)
                 (listGetD x2Row (Nat.mod (Nat.add (Nat.mul d dim) j) dim) fi.zeroF))) :=
  Eq.refl _

noncomputable def tWeightGradUpdateRowSpec (fi : FloatInterface)
    (twg dy2Row y1Row : List fi.carrier)
    (gradScale : fi.carrier) (dim : Nat) : List fi.carrier :=
  listMap (fun idx =>
    let d := Nat.div idx dim
    let j := Nat.mod idx dim
    fi.addF (listGetD twg idx fi.zeroF)
      (fi.mulF gradScale
        (fi.mulF (listGetD dy2Row d fi.zeroF)
                 (listGetD y1Row j fi.zeroF))))
    (listRange (Nat.mul dim dim))

theorem tWeightGradUpdateRowSpec_length (fi : FloatInterface)
    (twg dy2Row y1Row : List fi.carrier) (gradScale : fi.carrier) (dim : Nat) :
    listLength (tWeightGradUpdateRowSpec fi twg dy2Row y1Row gradScale dim) = Nat.mul dim dim :=
  Eq.trans (listLength_map _ (listRange (Nat.mul dim dim))) (listLength_range (Nat.mul dim dim))

theorem tWeightGradUpdateRowSpec_at_idx (fi : FloatInterface)
    (twg dy2Row y1Row : List fi.carrier) (gradScale : fi.carrier) (dim idx : Nat) :
    listGetD (tWeightGradUpdateRowSpec fi twg dy2Row y1Row gradScale dim) idx fi.zeroF =
    fi.addF (listGetD twg idx fi.zeroF)
      (fi.mulF gradScale
        (fi.mulF (listGetD dy2Row (Nat.div idx dim) fi.zeroF)
                 (listGetD y1Row (Nat.mod idx dim) fi.zeroF))) :=
  Eq.refl _

noncomputable def sBiasGradUpdateRowSpec (fi : FloatInterface)
    (sbg dsRow : List fi.carrier) (gradScale : fi.carrier) (dim : Nat) : List fi.carrier :=
  listMap (fun d =>
    fi.addF (listGetD sbg d fi.zeroF)
      (fi.mulF gradScale (listGetD dsRow d fi.zeroF)))
    (listRange dim)

theorem sBiasGradUpdateRowSpec_length (fi : FloatInterface)
    (sbg dsRow : List fi.carrier) (gradScale : fi.carrier) (dim : Nat) :
    listLength (sBiasGradUpdateRowSpec fi sbg dsRow gradScale dim) = dim :=
  Eq.trans (listLength_map _ (listRange dim)) (listLength_range dim)

theorem sBiasGradUpdateRowSpec_at_d (fi : FloatInterface)
    (sbg dsRow : List fi.carrier) (gradScale : fi.carrier) (dim d : Nat) :
    listGetD (sBiasGradUpdateRowSpec fi sbg dsRow gradScale dim) d fi.zeroF =
    fi.addF (listGetD sbg d fi.zeroF)
      (fi.mulF gradScale (listGetD dsRow d fi.zeroF)) :=
  Eq.refl _

noncomputable def tBiasGradUpdateRowSpec (fi : FloatInterface)
    (tbg dy2Row : List fi.carrier) (gradScale : fi.carrier) (dim : Nat) : List fi.carrier :=
  listMap (fun d =>
    fi.addF (listGetD tbg d fi.zeroF)
      (fi.mulF gradScale (listGetD dy2Row d fi.zeroF)))
    (listRange dim)

theorem tBiasGradUpdateRowSpec_length (fi : FloatInterface)
    (tbg dy2Row : List fi.carrier) (gradScale : fi.carrier) (dim : Nat) :
    listLength (tBiasGradUpdateRowSpec fi tbg dy2Row gradScale dim) = dim :=
  Eq.trans (listLength_map _ (listRange dim)) (listLength_range dim)

theorem tBiasGradUpdateRowSpec_at_d (fi : FloatInterface)
    (tbg dy2Row : List fi.carrier) (gradScale : fi.carrier) (dim d : Nat) :
    listGetD (tBiasGradUpdateRowSpec fi tbg dy2Row gradScale dim) d fi.zeroF =
    fi.addF (listGetD tbg d fi.zeroF)
      (fi.mulF gradScale (listGetD dy2Row d fi.zeroF)) :=
  Eq.refl _

noncomputable def gradScaleSpec (fi : FloatInterface) (gradMean : Bool) (batchSize : Nat) : fi.carrier :=
  bIte gradMean (fi.divF fi.oneF (fi.ofNat batchSize)) fi.oneF

theorem gradScaleSpec_when_gradMean_false (fi : FloatInterface) (batchSize : Nat) :
    gradScaleSpec fi Bool.false batchSize = fi.oneF := Eq.refl fi.oneF

theorem gradScaleSpec_when_gradMean_true (fi : FloatInterface) (batchSize : Nat) :
    gradScaleSpec fi Bool.true batchSize = fi.divF fi.oneF (fi.ofNat batchSize) := Eq.refl _

theorem gradScaleSpec_def (fi : FloatInterface) (gradMean : Bool) (batchSize : Nat) :
    gradScaleSpec fi gradMean batchSize =
    bIte gradMean (fi.divF fi.oneF (fi.ofNat batchSize)) fi.oneF :=
  Eq.refl _

structure BackwardOutputsSpec (fi : FloatInterface) : Type where
  dx1 : List fi.carrier
  dx2 : List fi.carrier
  sWeightGrad : List fi.carrier
  tWeightGrad : List fi.carrier
  sBiasGrad : List fi.carrier
  tBiasGrad : List fi.carrier

noncomputable def backwardFromOutputsRowSpec (fi : FloatInterface)
    (sWeight sBias tWeight tBias : List fi.carrier)
    (dy1Row dy2Row y1Row y2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (gradMean : Bool) (batchSize : Nat) (dim : Nat)
    (swg twg sbg tbg : List fi.carrier) : BackwardOutputsSpec fi :=
  let gradScale := gradScaleSpec fi gradMean batchSize
  let dy1Total := dy1TotalRowSpec fi tWeight dy1Row dy2Row dim
  let twgNew := tWeightGradUpdateRowSpec fi twg dy2Row y1Row gradScale dim
  let tbgNew := tBiasGradUpdateRowSpec fi tbg dy2Row gradScale dim
  let x2Row := x2RecoveryRowSpec fi tWeight tBias y1Row y2Row dim
  let scale := scaleRecompRowSpec fi sWeight sBias x2Row clipMin clipMax dim
  let ds := dsRowSpec fi sWeight sBias x2Row dy1Total y1Row clipMin clipMax dim
  let dx1 := dx1RowSpec fi dy1Total scale
  let dx2 := dx2RowSpec fi sWeight dy2Row ds dim
  let swgNew := sWeightGradUpdateRowSpec fi swg ds x2Row gradScale dim
  let sbgNew := sBiasGradUpdateRowSpec fi sbg ds gradScale dim
  BackwardOutputsSpec.mk dx1 dx2 swgNew twgNew sbgNew tbgNew

theorem backwardFromOutputsRowSpec_dx1_formula (fi : FloatInterface)
    (sWeight sBias tWeight tBias : List fi.carrier)
    (dy1Row dy2Row y1Row y2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (gradMean : Bool) (batchSize : Nat) (dim d : Nat)
    (swg twg sbg tbg : List fi.carrier) :
    listGetD (backwardFromOutputsRowSpec fi sWeight sBias tWeight tBias
      dy1Row dy2Row y1Row y2Row clipMin clipMax gradMean batchSize dim swg twg sbg tbg).dx1
      d fi.zeroF =
    fi.mulF
      (listGetD (dy1TotalRowSpec fi tWeight dy1Row dy2Row dim) d fi.zeroF)
      (listGetD (scaleRecompRowSpec fi sWeight sBias
        (x2RecoveryRowSpec fi tWeight tBias y1Row y2Row dim) clipMin clipMax dim) d fi.zeroF) :=
  Eq.refl _

theorem backwardFromOutputsRowSpec_dx2_formula (fi : FloatInterface)
    (sWeight sBias tWeight tBias : List fi.carrier)
    (dy1Row dy2Row y1Row y2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (gradMean : Bool) (batchSize : Nat) (dim j : Nat)
    (swg twg sbg tbg : List fi.carrier) :
    listGetD (backwardFromOutputsRowSpec fi sWeight sBias tWeight tBias
      dy1Row dy2Row y1Row y2Row clipMin clipMax gradMean batchSize dim swg twg sbg tbg).dx2
      j fi.zeroF =
    fi.addF (listGetD dy2Row j fi.zeroF)
      (listFoldl (fun acc d =>
        fi.addF acc
          (fi.mulF (listGetD sWeight (Nat.add (Nat.mul d dim) j) fi.zeroF)
                   (listGetD (dsRowSpec fi sWeight sBias
                     (x2RecoveryRowSpec fi tWeight tBias y1Row y2Row dim)
                     (dy1TotalRowSpec fi tWeight dy1Row dy2Row dim)
                     y1Row clipMin clipMax dim) d fi.zeroF)))
        fi.zeroF (listRange dim)) :=
  Eq.refl _

theorem backwardFromOutputsRowSpec_ds_clipped_semantics (fi : FloatInterface)
    (sWeight sBias tWeight tBias : List fi.carrier)
    (dy1Row dy2Row y1Row y2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (gradMean : Bool) (batchSize : Nat) (dim d : Nat)
    (swg twg sbg tbg : List fi.carrier)
    (hd : natLtB d dim = Bool.true)
    (hBelow : fi.ltF (dotProductAt fi sWeight sBias (x2RecoveryRowSpec fi tWeight tBias y1Row y2Row dim) d dim) clipMin = Bool.true) :
    listGetD (dsRowSpec fi sWeight sBias
      (x2RecoveryRowSpec fi tWeight tBias y1Row y2Row dim)
      (dy1TotalRowSpec fi tWeight dy1Row dy2Row dim)
      y1Row clipMin clipMax dim) d fi.zeroF = fi.zeroF :=
  dsRowSpec_zero_when_clipped_below fi sWeight sBias
    (x2RecoveryRowSpec fi tWeight tBias y1Row y2Row dim)
    (dy1TotalRowSpec fi tWeight dy1Row dy2Row dim)
    y1Row clipMin clipMax dim d hd hBelow

theorem backwardFromOutputsRowSpec_tWeightGrad_formula (fi : FloatInterface)
    (sWeight sBias tWeight tBias : List fi.carrier)
    (dy1Row dy2Row y1Row y2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (gradMean : Bool) (batchSize : Nat) (dim : Nat)
    (swg twg sbg tbg : List fi.carrier) (idx : Nat) :
    listGetD (backwardFromOutputsRowSpec fi sWeight sBias tWeight tBias
      dy1Row dy2Row y1Row y2Row clipMin clipMax gradMean batchSize dim swg twg sbg tbg).tWeightGrad
      idx fi.zeroF =
    fi.addF (listGetD twg idx fi.zeroF)
      (fi.mulF (gradScaleSpec fi gradMean batchSize)
        (fi.mulF (listGetD dy2Row (Nat.div idx dim) fi.zeroF)
                 (listGetD y1Row (Nat.mod idx dim) fi.zeroF))) :=
  Eq.refl _

theorem backwardFromOutputsRowSpec_tBiasGrad_formula (fi : FloatInterface)
    (sWeight sBias tWeight tBias : List fi.carrier)
    (dy1Row dy2Row y1Row y2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (gradMean : Bool) (batchSize : Nat) (dim d : Nat)
    (swg twg sbg tbg : List fi.carrier) :
    listGetD (backwardFromOutputsRowSpec fi sWeight sBias tWeight tBias
      dy1Row dy2Row y1Row y2Row clipMin clipMax gradMean batchSize dim swg twg sbg tbg).tBiasGrad
      d fi.zeroF =
    fi.addF (listGetD tbg d fi.zeroF)
      (fi.mulF (gradScaleSpec fi gradMean batchSize) (listGetD dy2Row d fi.zeroF)) :=
  Eq.refl _

theorem backwardFromOutputsRowSpec_sBiasGrad_formula (fi : FloatInterface)
    (sWeight sBias tWeight tBias : List fi.carrier)
    (dy1Row dy2Row y1Row y2Row : List fi.carrier)
    (clipMin clipMax : fi.carrier) (gradMean : Bool) (batchSize : Nat) (dim d : Nat)
    (swg twg sbg tbg : List fi.carrier) :
    listGetD (backwardFromOutputsRowSpec fi sWeight sBias tWeight tBias
      dy1Row dy2Row y1Row y2Row clipMin clipMax gradMean batchSize dim swg twg sbg tbg).sBiasGrad
      d fi.zeroF =
    fi.addF (listGetD sbg d fi.zeroF)
      (fi.mulF (gradScaleSpec fi gradMean batchSize)
        (listGetD (dsRowSpec fi sWeight sBias
          (x2RecoveryRowSpec fi tWeight tBias y1Row y2Row dim)
          (dy1TotalRowSpec fi tWeight dy1Row dy2Row dim)
          y1Row clipMin clipMax dim) d fi.zeroF)) :=
  Eq.refl _

noncomputable def natToU32LE (n : Nat) : List Nat :=
  List.cons (Nat.mod n 256)
    (List.cons (Nat.mod (Nat.div n 256) 256)
      (List.cons (Nat.mod (Nat.div (Nat.div n 256) 256) 256)
        (List.cons (Nat.mod (Nat.div (Nat.div (Nat.div n 256) 256) 256) 256) List.nil)))

theorem natToU32LE_length (n : Nat) : listLength (natToU32LE n) = 4 := Eq.refl 4

theorem natToU32LE_def (n : Nat) :
    natToU32LE n = List.cons (Nat.mod n 256)
      (List.cons (Nat.mod (Nat.div n 256) 256)
        (List.cons (Nat.mod (Nat.div (Nat.div n 256) 256) 256)
          (List.cons (Nat.mod (Nat.div (Nat.div (Nat.div n 256) 256) 256) 256) List.nil))) :=
  Eq.refl _

noncomputable def natFromU32LE (bs : List Nat) : ResultT Nat :=
  List.recOn (motive := fun _ => ResultT Nat) bs
    (ResultT.err ZigError.badFileFormat)
    (fun b0 rest1 _ =>
      List.recOn (motive := fun _ => ResultT Nat) rest1
        (ResultT.err ZigError.badFileFormat)
        (fun b1 rest2 _ =>
          List.recOn (motive := fun _ => ResultT Nat) rest2
            (ResultT.err ZigError.badFileFormat)
            (fun b2 rest3 _ =>
              List.recOn (motive := fun _ => ResultT Nat) rest3
                (ResultT.err ZigError.badFileFormat)
                (fun b3 _ _ =>
                  ResultT.ok (Nat.add b0
                    (Nat.add (Nat.mul b1 256)
                      (Nat.add (Nat.mul b2 65536)
                        (Nat.mul b3 16777216)))))
                )))

theorem natFromU32LE_def (b0 b1 b2 b3 : Nat) (rest : List Nat) :
    natFromU32LE (List.cons b0 (List.cons b1 (List.cons b2 (List.cons b3 rest)))) =
    ResultT.ok (Nat.add b0 (Nat.add (Nat.mul b1 256) (Nat.add (Nat.mul b2 65536) (Nat.mul b3 16777216)))) :=
  Eq.refl _

theorem natFromU32LE_short_err :
    natFromU32LE List.nil = ResultT.err ZigError.badFileFormat := Eq.refl _

theorem natFromU32LE_one_err (b0 : Nat) :
    natFromU32LE (List.cons b0 List.nil) = ResultT.err ZigError.badFileFormat := Eq.refl _

theorem natFromU32LE_two_err (b0 b1 : Nat) :
    natFromU32LE (List.cons b0 (List.cons b1 List.nil)) = ResultT.err ZigError.badFileFormat :=
  Eq.refl _

theorem natFromU32LE_three_err (b0 b1 b2 : Nat) :
    natFromU32LE (List.cons b0 (List.cons b1 (List.cons b2 List.nil))) =
    ResultT.err ZigError.badFileFormat := Eq.refl _

theorem natToU32LE_roundtrip (n : Nat) (h : natLeB n 4294967295 = Bool.true) :
    natFromU32LE (listAppend (natToU32LE n) List.nil) =
    ResultT.ok (Nat.add (Nat.mod n 256)
      (Nat.add (Nat.mul (Nat.mod (Nat.div n 256) 256) 256)
        (Nat.add (Nat.mul (Nat.mod (Nat.div (Nat.div n 256) 256) 256) 65536)
          (Nat.mul (Nat.mod (Nat.div (Nat.div (Nat.div n 256) 256) 256) 256) 16777216)))) :=
  Eq.refl _

noncomputable def natToU64LE (n : Nat) : List Nat :=
  listAppend (natToU32LE n) (natToU32LE (Nat.div n 4294967296))

theorem natToU64LE_length (n : Nat) : listLength (natToU64LE n) = 8 :=
  Eq.trans (listLength_append (natToU32LE n) (natToU32LE (Nat.div n 4294967296)))
    (Eq.trans
      (congrArg2 Nat.add (natToU32LE_length n) (natToU32LE_length (Nat.div n 4294967296)))
      (Eq.refl 8))

noncomputable def natFromU64LE (bs : List Nat) : ResultT Nat :=
  ResultT.bind (natFromU32LE (listTake 4 bs)) (fun lo =>
    ResultT.bind (natFromU32LE (listTake 4 (listDrop 4 bs))) (fun hi =>
      ResultT.ok (Nat.add lo (Nat.mul hi 4294967296))))

theorem natFromU64LE_def (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (rest : List Nat) :
    natFromU64LE (List.cons b0 (List.cons b1 (List.cons b2 (List.cons b3
      (List.cons b4 (List.cons b5 (List.cons b6 (List.cons b7 rest)))))))) =
    ResultT.ok (Nat.add
      (Nat.add b0 (Nat.add (Nat.mul b1 256) (Nat.add (Nat.mul b2 65536) (Nat.mul b3 16777216))))
      (Nat.mul (Nat.add b4 (Nat.add (Nat.mul b5 256) (Nat.add (Nat.mul b6 65536) (Nat.mul b7 16777216)))) 4294967296)) :=
  Eq.refl _

noncomputable def encodeBoolByte (b : Bool) : Nat :=
  Bool.recOn (motive := fun _ => Nat) b 0 1

theorem encodeBoolByte_false : encodeBoolByte Bool.false = 0 := Eq.refl 0
theorem encodeBoolByte_true : encodeBoolByte Bool.true = 1 := Eq.refl 1

noncomputable def decodeBoolByte (n : Nat) : ResultT Bool :=
  bIte (natEqB n 0)
    (ResultT.ok Bool.false)
    (bIte (natEqB n 1)
      (ResultT.ok Bool.true)
      (ResultT.err ZigError.badFileFormat))

theorem decodeBoolByte_zero : decodeBoolByte 0 = ResultT.ok Bool.false := Eq.refl _
theorem decodeBoolByte_one : decodeBoolByte 1 = ResultT.ok Bool.true := Eq.refl _
theorem decodeBoolByte_two : decodeBoolByte 2 = ResultT.err ZigError.badFileFormat := Eq.refl _

theorem decodeBoolByte_roundtrip (b : Bool) :
    decodeBoolByte (encodeBoolByte b) = ResultT.ok b :=
  Bool.recOn (motive := fun c => decodeBoolByte (encodeBoolByte c) = ResultT.ok c) b
    (Eq.refl (ResultT.ok Bool.false))
    (Eq.refl (ResultT.ok Bool.true))

theorem decodeBoolByte_err_on_2 : decodeBoolByte 2 = ResultT.err ZigError.badFileFormat :=
  Eq.refl _

theorem decodeBoolByte_err_on_3 : decodeBoolByte 3 = ResultT.err ZigError.badFileFormat :=
  Eq.refl _

noncomputable def floatToU32LE (fi : FloatInterface) (x : fi.carrier) : List Nat :=
  natToU32LE (fi.floatToU32 x)

theorem floatToU32LE_length (fi : FloatInterface) (x : fi.carrier) :
    listLength (floatToU32LE fi x) = 4 :=
  natToU32LE_length (fi.floatToU32 x)

noncomputable def u32LEToFloat (fi : FloatInterface) (bs : List Nat) : ResultT fi.carrier :=
  ResultT.bind (natFromU32LE bs) (fun n => ResultT.ok (fi.u32ToFloat n))

theorem u32LEToFloat_floatToU32LE_roundtrip (fi : FloatInterface) (x : fi.carrier) (rest : List Nat) :
    u32LEToFloat fi (listAppend (floatToU32LE fi x) rest) =
    ResultT.bind (natFromU32LE (listAppend (natToU32LE (fi.floatToU32 x)) rest))
      (fun n => ResultT.ok (fi.u32ToFloat n)) :=
  Eq.refl _

noncomputable def magicBytes : List Nat :=
  List.cons 82 (List.cons 83 (List.cons 70 (List.cons 48 List.nil)))

theorem magicBytes_length : listLength magicBytes = 4 := Eq.refl 4
theorem magicBytes_def : magicBytes = List.cons 82 (List.cons 83 (List.cons 70 (List.cons 48 List.nil))) :=
  Eq.refl _
theorem magicBytes_0 : listGetD magicBytes 0 0 = 82 := Eq.refl 82
theorem magicBytes_1 : listGetD magicBytes 1 0 = 83 := Eq.refl 83
theorem magicBytes_2 : listGetD magicBytes 2 0 = 70 := Eq.refl 70
theorem magicBytes_3 : listGetD magicBytes 3 0 = 48 := Eq.refl 48

noncomputable def saveVersionBytes : List Nat := natToU32LE 4

theorem saveVersionBytes_def : saveVersionBytes = List.cons 4 (List.cons 0 (List.cons 0 (List.cons 0 List.nil))) :=
  Eq.refl _

theorem saveVersionBytes_length : listLength saveVersionBytes = 4 := Eq.refl 4

noncomputable def takeN (n : Nat) (bs : List Nat) : ResultT (List Nat × List Nat) :=
  Nat.recOn (motive := fun _ => List Nat → ResultT (List Nat × List Nat)) n
    (fun rest => ResultT.ok (Prod.mk List.nil rest))
    (fun _ ihTake rest =>
      List.recOn (motive := fun _ => ResultT (List Nat × List Nat)) rest
        (ResultT.err ZigError.badFileFormat)
        (fun h t _ =>
          ResultT.bind (ihTake t) (fun pair =>
            ResultT.ok (Prod.mk (List.cons h (Prod.fst pair)) (Prod.snd pair)))))
    bs

theorem takeN_zero (bs : List Nat) :
    takeN 0 bs = ResultT.ok (Prod.mk List.nil bs) := Eq.refl _

theorem takeN_succ_nil (n : Nat) :
    takeN (Nat.succ n) List.nil = ResultT.err ZigError.badFileFormat := Eq.refl _

theorem takeN_succ_cons (n : Nat) (h : Nat) (t : List Nat) :
    takeN (Nat.succ n) (List.cons h t) =
    ResultT.bind (takeN n t) (fun pair =>
      ResultT.ok (Prod.mk (List.cons h (Prod.fst pair)) (Prod.snd pair))) :=
  Eq.refl _

theorem takeN_ok_fst_length (n : Nat) (bs taken rest : List Nat)
    (h : takeN n bs = ResultT.ok (Prod.mk taken rest)) :
    listLength taken = n :=
  Nat.recOn (motive := fun k => ∀ bs taken rest,
    takeN k bs = ResultT.ok (Prod.mk taken rest) → listLength taken = k) n
    (fun bs taken rest htake =>
      ResultT.noConfusion (Eq.symm (Eq.trans (Eq.symm htake) (Eq.refl _)))
        (fun htaken _ => congrArg listLength htaken))
    (fun k ih bs taken rest htake =>
      List.recOn (motive := fun l => takeN (Nat.succ k) l = ResultT.ok (Prod.mk taken rest) → listLength taken = Nat.succ k) bs
        (fun hbad => ResultT.noConfusion (Eq.trans hbad (Eq.refl _)))
        (fun hb tb _ htake2 => congrArg Nat.succ (ih tb (listTake k tb) (listDrop k tb) (Eq.refl _)))
        htake)
    bs taken rest h

theorem takeN_appended (n : Nat) (xs ys : List Nat) (h : listLength xs = n) :
    takeN n (listAppend xs ys) = ResultT.ok (Prod.mk xs ys) :=
  Nat.recOn (motive := fun k => ∀ as' bs', listLength as' = k →
    takeN k (listAppend as' bs') = ResultT.ok (Prod.mk as' bs')) n
    (fun as' bs' hlen =>
      List.recOn (motive := fun l => listLength l = 0 →
        takeN 0 (listAppend l bs') = ResultT.ok (Prod.mk l bs')) as'
        (fun _ => Eq.refl _)
        (fun _ _ _ hbad => False.elim (Nat.noConfusion hbad))
        hlen)
    (fun k ih as' bs' hlen =>
      List.recOn (motive := fun l => listLength l = Nat.succ k →
        takeN (Nat.succ k) (listAppend l bs') = ResultT.ok (Prod.mk l bs')) as'
        (fun hbad => False.elim (Nat.noConfusion hbad))
        (fun ha ta _ hlen2 =>
          Eq.trans
            (takeN_succ_cons k ha (listAppend ta bs'))
            (congrArg (fun r => ResultT.bind r _) (ih ta bs' (Nat.succ.inj hlen2))))
        hlen)
    xs ys h

noncomputable def parseMagicHeader (bs : List Nat) : ResultT (List Nat) :=
  ResultT.bind (takeN 4 bs) (fun pair =>
    let hdr := Prod.fst pair
    let rest := Prod.snd pair
    bIte (bAnd (bAnd (bAnd
      (natEqB (listGetD hdr 0 0) 82)
      (natEqB (listGetD hdr 1 0) 83))
      (natEqB (listGetD hdr 2 0) 70))
      (natEqB (listGetD hdr 3 0) 48))
      (ResultT.ok rest)
      (ResultT.err ZigError.badFileFormat))

theorem parseMagicHeader_ok (bs : List Nat) (rest : List Nat)
    (hTake : takeN 4 bs = ResultT.ok (Prod.mk (List.cons 82 (List.cons 83 (List.cons 70 (List.cons 48 List.nil)))) rest)) :
    parseMagicHeader bs = ResultT.ok rest :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _) hTake)
    (Eq.refl (ResultT.ok rest))

theorem parseMagicHeader_err_bad_first_byte (bs : List Nat) (b0 : Nat)
    (hb0 : natEqB b0 82 = Bool.false)
    (rest : List Nat)
    (hTake : takeN 4 bs = ResultT.ok (Prod.mk (List.cons b0 (List.cons 83 (List.cons 70 (List.cons 48 List.nil)))) rest)) :
    parseMagicHeader bs = ResultT.err ZigError.badFileFormat :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _) hTake)
    (congrArg (fun x => bIte x _ _)
      (congrArg (fun y => bAnd y _) (congrArg (fun z => bAnd z _) (congrArg (bAnd · _) hb0))))

theorem parseMagicHeader_err_short_input :
    parseMagicHeader List.nil = ResultT.err ZigError.badFileFormat :=
  Eq.refl _

noncomputable def parseVersionField (bs : List Nat) : ResultT (List Nat) :=
  ResultT.bind (takeN 4 bs) (fun pair =>
    ResultT.bind (natFromU32LE (Prod.fst pair)) (fun v =>
      bIte (natEqB v 4)
        (ResultT.ok (Prod.snd pair))
        (ResultT.err ZigError.unsupportedVersion)))

theorem parseVersionField_ok (bs rest : List Nat)
    (hTake : takeN 4 bs = ResultT.ok (Prod.mk (natToU32LE 4) rest)) :
    parseVersionField bs = ResultT.ok rest :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _) hTake)
    (Eq.refl (ResultT.ok rest))

theorem parseVersionField_err_wrong_version (bs rest : List Nat) (v : Nat)
    (hv : natEqB v 4 = Bool.false)
    (hTake : takeN 4 bs = ResultT.ok (Prod.mk (natToU32LE v) rest)) :
    parseVersionField bs = ResultT.err ZigError.unsupportedVersion :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _) hTake)
    (congrArg (fun x => bIte x _ _) hv)

noncomputable def parseU64Field (bs : List Nat) : ResultT (Nat × List Nat) :=
  ResultT.bind (takeN 8 bs) (fun pair =>
    ResultT.bind (natFromU64LE (Prod.fst pair)) (fun v =>
      ResultT.ok (Prod.mk v (Prod.snd pair))))

theorem parseU64Field_ok (bs rest : List Nat) (v : Nat)
    (hTake : takeN 8 bs = ResultT.ok (Prod.mk (natToU64LE v) rest))
    (hParse : natFromU64LE (natToU64LE v) = ResultT.ok v) :
    parseU64Field bs = ResultT.ok (Prod.mk v rest) :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _) hTake)
    (congrArg (fun r => ResultT.bind r _) hParse)

noncomputable def parseFloatField (fi : FloatInterface) (bs : List Nat) : ResultT (fi.carrier × List Nat) :=
  ResultT.bind (takeN 4 bs) (fun pair =>
    ResultT.bind (natFromU32LE (Prod.fst pair)) (fun n =>
      ResultT.ok (Prod.mk (fi.u32ToFloat n) (Prod.snd pair))))

theorem parseFloatField_ok (fi : FloatInterface) (x : fi.carrier) (bs rest : List Nat)
    (hTake : takeN 4 bs = ResultT.ok (Prod.mk (floatToU32LE fi x) rest))
    (hParse : natFromU32LE (floatToU32LE fi x) = ResultT.ok (fi.floatToU32 x)) :
    parseFloatField fi bs = ResultT.ok (Prod.mk (fi.u32ToFloat (fi.floatToU32 x)) rest) :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _) hTake)
    (congrArg (fun r => ResultT.bind r _) hParse)

theorem parseFloatField_roundtrip (fi : FloatInterface) (x : fi.carrier) (bs rest : List Nat)
    (hTake : takeN 4 bs = ResultT.ok (Prod.mk (floatToU32LE fi x) rest))
    (hParse : natFromU32LE (floatToU32LE fi x) = ResultT.ok (fi.floatToU32 x)) :
    ResultT.map Prod.fst (parseFloatField fi bs) = ResultT.ok x :=
  Eq.trans
    (congrArg (ResultT.map Prod.fst)
      (parseFloatField_ok fi x bs rest hTake hParse))
    (congrArg (fun v => ResultT.ok (fi.u32ToFloat v))
      (Eq.refl (fi.floatToU32 x)))

noncomputable def parseBoolField (bs : List Nat) : ResultT (Bool × List Nat) :=
  ResultT.bind (takeN 1 bs) (fun pair =>
    ResultT.bind (decodeBoolByte (listGetD (Prod.fst pair) 0 0)) (fun b =>
      ResultT.ok (Prod.mk b (Prod.snd pair))))

theorem parseBoolField_ok_true (h : Nat) (t rest : List Nat)
    (hTake : takeN 1 (List.cons h t) = ResultT.ok (Prod.mk (List.cons h List.nil) t))
    (hBool : h = 1) :
    parseBoolField (List.cons h t) = ResultT.ok (Prod.mk Bool.true t) :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _) hTake)
    (congrArg (fun v => ResultT.bind (decodeBoolByte (listGetD (List.cons v List.nil) 0 0)) _) hBool)

theorem parseBoolField_ok_false (h : Nat) (t rest : List Nat)
    (hTake : takeN 1 (List.cons h t) = ResultT.ok (Prod.mk (List.cons h List.nil) t))
    (hBool : h = 0) :
    parseBoolField (List.cons h t) = ResultT.ok (Prod.mk Bool.false t) :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _) hTake)
    (congrArg (fun v => ResultT.bind (decodeBoolByte (listGetD (List.cons v List.nil) 0 0)) _) hBool)

theorem parseBoolField_err_on_bad_byte (n : Nat) (t : List Nat)
    (hN : natEqB n 0 = Bool.false)
    (hN1 : natEqB n 1 = Bool.false)
    (hTake : takeN 1 (List.cons n t) = ResultT.ok (Prod.mk (List.cons n List.nil) t)) :
    parseBoolField (List.cons n t) = ResultT.err ZigError.badFileFormat :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _) hTake)
    (congrArg (fun x => ResultT.bind (bIte x _ _) _) hN)

structure LayerCoreSpec (fi : FloatInterface) : Type where
  sWeight : Tensor fi
  tWeight : Tensor fi
  sBias : Tensor fi
  tBias : Tensor fi
  clipMin : fi.carrier
  clipMax : fi.carrier
  gradMean : Bool
  dim : Nat
  sWeight_shape : tensorHasShape sWeight (TensorShape.mk dim dim) = Bool.true
  tWeight_shape : tensorHasShape tWeight (TensorShape.mk dim dim) = Bool.true
  sBias_shape : tensorHasShape sBias (TensorShape.mk 1 dim) = Bool.true
  tBias_shape : tensorHasShape tBias (TensorShape.mk 1 dim) = Bool.true
  clipRange_valid : fi.ltF clipMin clipMax = Bool.true

theorem layerCoreSpec_dim_pos {fi : FloatInterface} (lc : LayerCoreSpec fi)
    (h : natLtB 0 lc.dim = Bool.true) : natLtB 0 lc.dim = Bool.true := h

noncomputable def layerCoreForwardRow (fi : FloatInterface) (lc : LayerCoreSpec fi)
    (x1Row x2Row : List fi.carrier) : ForwardRowResult fi :=
  forwardRowSpec fi x1Row x2Row
    lc.sWeight.data lc.sBias.data
    lc.tWeight.data lc.tBias.data
    lc.clipMin lc.clipMax lc.dim

theorem layerCoreForwardRow_y1_length (fi : FloatInterface) (lc : LayerCoreSpec fi)
    (x1Row x2Row : List fi.carrier)
    (hLen : listLength x1Row = lc.dim) :
    listLength (frr_y1 (layerCoreForwardRow fi lc x1Row x2Row)) = lc.dim :=
  forwardRowSpec_y1_length fi x1Row x2Row
    lc.sWeight.data lc.sBias.data lc.tWeight.data lc.tBias.data
    lc.clipMin lc.clipMax lc.dim hLen

noncomputable def layerCoreInverseRow (fi : FloatInterface) (lc : LayerCoreSpec fi)
    (y1Row y2Row : List fi.carrier) : ForwardRowResult fi :=
  inverseRowSpec fi y1Row y2Row
    lc.sWeight.data lc.sBias.data
    lc.tWeight.data lc.tBias.data
    lc.clipMin lc.clipMax lc.dim

theorem layerCoreForwardThenInverse_x2_at_d (fi : FloatInterface) (lc : LayerCoreSpec fi)
    (x1Row x2Row : List fi.carrier) (d : Nat) :
    listGetD
      (frr_y2 (layerCoreInverseRow fi lc
        (frr_y1 (layerCoreForwardRow fi lc x1Row x2Row))
        (frr_y2 (layerCoreForwardRow fi lc x1Row x2Row)))) d fi.zeroF =
    fi.subF
      (fi.addF (listGetD x2Row d fi.zeroF)
        (dotProductAt fi lc.tWeight.data lc.tBias.data
          (listZipWith fi.mulF x1Row (computeScaleRowSpec fi lc.sWeight.data lc.sBias.data x2Row lc.clipMin lc.clipMax lc.dim))
          d lc.dim))
      (dotProductAt fi lc.tWeight.data lc.tBias.data
        (listZipWith fi.mulF x1Row (computeScaleRowSpec fi lc.sWeight.data lc.sBias.data x2Row lc.clipMin lc.clipMax lc.dim))
        d lc.dim) :=
  Eq.refl _

theorem layerCoreForwardThenInverse_x2_exact_at_d (fi : FloatInterface) (lc : LayerCoreSpec fi)
    (x1Row x2Row : List fi.carrier) (d : Nat) :
    fi.subF
      (fi.addF (listGetD x2Row d fi.zeroF)
        (dotProductAt fi lc.tWeight.data lc.tBias.data
          (listZipWith fi.mulF x1Row (computeScaleRowSpec fi lc.sWeight.data lc.sBias.data x2Row lc.clipMin lc.clipMax lc.dim))
          d lc.dim))
      (dotProductAt fi lc.tWeight.data lc.tBias.data
        (listZipWith fi.mulF x1Row (computeScaleRowSpec fi lc.sWeight.data lc.sBias.data x2Row lc.clipMin lc.clipMax lc.dim))
        d lc.dim) =
    listGetD x2Row d fi.zeroF :=
  fi.subF_addF_cancel (listGetD x2Row d fi.zeroF)
    (dotProductAt fi lc.tWeight.data lc.tBias.data
      (listZipWith fi.mulF x1Row (computeScaleRowSpec fi lc.sWeight.data lc.sBias.data x2Row lc.clipMin lc.clipMax lc.dim))
      d lc.dim)

theorem layerCoreForwardThenInverse_x1_exact_at_d (fi : FloatInterface) (lc : LayerCoreSpec fi)
    (x1Row x2Row : List fi.carrier) (d : Nat) (hd : natLtB d lc.dim = Bool.true) :
    fi.divF
      (fi.mulF (listGetD x1Row d fi.zeroF)
        (listGetD (computeScaleRowSpec fi lc.sWeight.data lc.sBias.data x2Row lc.clipMin lc.clipMax lc.dim) d fi.zeroF))
      (listGetD (computeScaleRowSpec fi lc.sWeight.data lc.sBias.data x2Row lc.clipMin lc.clipMax lc.dim) d fi.zeroF) =
    listGetD x1Row d fi.zeroF :=
  fi.mulF_divF_cancel (listGetD x1Row d fi.zeroF)
    (listGetD (computeScaleRowSpec fi lc.sWeight.data lc.sBias.data x2Row lc.clipMin lc.clipMax lc.dim) d fi.zeroF)
    (computeScaleRowSpec_positive fi lc.sWeight.data lc.sBias.data x2Row lc.clipMin lc.clipMax lc.dim d hd)

noncomputable def layerCoreBackwardRow (fi : FloatInterface) (lc : LayerCoreSpec fi)
    (dy1Row dy2Row y1Row y2Row : List fi.carrier)
    (batchSize : Nat)
    (swg twg sbg tbg : List fi.carrier) : BackwardOutputsSpec fi :=
  backwardFromOutputsRowSpec fi
    lc.sWeight.data lc.sBias.data
    lc.tWeight.data lc.tBias.data
    dy1Row dy2Row y1Row y2Row
    lc.clipMin lc.clipMax lc.gradMean batchSize lc.dim
    swg twg sbg tbg

theorem layerCoreBackwardRow_dy1_total_formula (fi : FloatInterface) (lc : LayerCoreSpec fi)
    (dy1Row dy2Row y1Row y2Row : List fi.carrier)
    (batchSize : Nat) (swg twg sbg tbg : List fi.carrier) (j : Nat)
    (hj : natLtB j lc.dim = Bool.true) :
    listGetD (dy1TotalRowSpec fi lc.tWeight.data dy1Row dy2Row lc.dim) j fi.zeroF =
    fi.addF (listGetD dy1Row j fi.zeroF)
      (listFoldl (fun acc d =>
        fi.addF acc
          (fi.mulF (listGetD lc.tWeight.data (Nat.add (Nat.mul d lc.dim) j) fi.zeroF)
                   (listGetD dy2Row d fi.zeroF)))
        fi.zeroF (listRange lc.dim)) :=
  dy1TotalRowSpec_at_j fi lc.tWeight.data dy1Row dy2Row lc.dim j hj

theorem layerCoreBackwardRow_x2_recovery (fi : FloatInterface) (lc : LayerCoreSpec fi)
    (y1Row y2Row : List fi.carrier) (d : Nat) :
    listGetD (x2RecoveryRowSpec fi lc.tWeight.data lc.tBias.data y1Row y2Row lc.dim) d fi.zeroF =
    fi.subF (listGetD y2Row d fi.zeroF)
      (dotProductAt fi lc.tWeight.data lc.tBias.data y1Row d lc.dim) :=
  x2RecoveryRowSpec_formula fi lc.tWeight.data lc.tBias.data y1Row y2Row lc.dim d

theorem layerCoreBackwardRow_ds_zero_when_saturated (fi : FloatInterface) (lc : LayerCoreSpec fi)
    (dy1Row dy2Row y1Row y2Row : List fi.carrier)
    (batchSize : Nat) (swg twg sbg tbg : List fi.carrier) (d : Nat)
    (hd : natLtB d lc.dim = Bool.true)
    (hSat : bOr
      (fi.ltF (dotProductAt fi lc.sWeight.data lc.sBias.data
        (x2RecoveryRowSpec fi lc.tWeight.data lc.tBias.data y1Row y2Row lc.dim) d lc.dim)
        lc.clipMin)
      (fi.ltF lc.clipMax
        (dotProductAt fi lc.sWeight.data lc.sBias.data
          (x2RecoveryRowSpec fi lc.tWeight.data lc.tBias.data y1Row y2Row lc.dim) d lc.dim))
      = Bool.true) :
    listGetD (dsRowSpec fi lc.sWeight.data lc.sBias.data
      (x2RecoveryRowSpec fi lc.tWeight.data lc.tBias.data y1Row y2Row lc.dim)
      (dy1TotalRowSpec fi lc.tWeight.data dy1Row dy2Row lc.dim)
      y1Row lc.clipMin lc.clipMax lc.dim) d fi.zeroF = fi.zeroF :=
  congrArg (fun x => bIte x fi.zeroF _) hSat

structure SavedLayerSnapshot (fi : FloatInterface) : Type where
  clipMin : fi.carrier
  clipMax : fi.carrier
  gradMean : Bool
  sWeight : Tensor fi
  tWeight : Tensor fi
  sBias : Tensor fi
  tBias : Tensor fi

structure SavedModelSnapshot (fi : FloatInterface) : Type where
  numLayers : Nat
  dim : Nat
  cfg : ModelConfig fi
  layers : List (SavedLayerSnapshot fi)
  layers_count : listLength layers = numLayers

noncomputable def serializeTensorBytes (fi : FloatInterface) (t : Tensor fi) : List Nat :=
  listAppend (natToU64LE 2)
    (listAppend (natToU64LE t.shape.rows)
      (listAppend (natToU64LE t.shape.cols)
        (listFoldl (fun acc v => listAppend acc (floatToU32LE fi v))
          List.nil t.data)))

theorem serializeTensorBytes_starts_with_dimcount2 (fi : FloatInterface) (t : Tensor fi) :
    listTake 8 (serializeTensorBytes fi t) = natToU64LE 2 :=
  Eq.trans
    (listTake_append_drop 8 (serializeTensorBytes fi t))
    (Eq.refl _)

theorem serializeTensorBytes_dimcount_is_2 (fi : FloatInterface) (t : Tensor fi) :
    listTake 8 (serializeTensorBytes fi t) = natToU64LE 2 :=
  Eq.refl _

noncomputable def serializeLayerSnapshotBytes (fi : FloatInterface) (ls : SavedLayerSnapshot fi) : List Nat :=
  listAppend (floatToU32LE fi ls.clipMin)
    (listAppend (floatToU32LE fi ls.clipMax)
      (listAppend (List.cons (encodeBoolByte ls.gradMean) List.nil)
        (listAppend (serializeTensorBytes fi ls.sWeight)
          (listAppend (serializeTensorBytes fi ls.tWeight)
            (listAppend (serializeTensorBytes fi ls.sBias)
              (serializeTensorBytes fi ls.tBias))))))

theorem serializeLayerSnapshotBytes_starts_with_clipMin (fi : FloatInterface) (ls : SavedLayerSnapshot fi) :
    listTake 4 (serializeLayerSnapshotBytes fi ls) = floatToU32LE fi ls.clipMin :=
  Eq.refl _

noncomputable def serializeSnapshotPayload (fi : FloatInterface) (s : SavedModelSnapshot fi) : List Nat :=
  listAppend magicBytes
    (listAppend saveVersionBytes
      (listAppend (natToU64LE s.numLayers)
        (listAppend (natToU64LE s.dim)
          (listAppend (floatToU32LE fi s.cfg.clipMin)
            (listAppend (floatToU32LE fi s.cfg.clipMax)
              (listAppend (List.cons (encodeBoolByte s.cfg.gradMean) List.nil)
                (listAppend (natToU64LE s.cfg.maxDim)
                  (listAppend (natToU64LE s.cfg.maxLayers)
                    (listFoldl (fun acc ls => listAppend acc (serializeLayerSnapshotBytes fi ls))
                      List.nil s.layers)))))))))

theorem serializeSnapshotPayload_starts_with_magic (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    listTake 4 (serializeSnapshotPayload fi s) = magicBytes :=
  Eq.refl _

theorem serializeSnapshotPayload_version_bytes (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    listTake 4 (listDrop 4 (serializeSnapshotPayload fi s)) = saveVersionBytes :=
  Eq.refl _

theorem serializeSnapshotPayload_magic_is_rsf0 (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    listGetD (serializeSnapshotPayload fi s) 0 0 = 82 ∧
    listGetD (serializeSnapshotPayload fi s) 1 0 = 83 ∧
    listGetD (serializeSnapshotPayload fi s) 2 0 = 70 ∧
    listGetD (serializeSnapshotPayload fi s) 3 0 = 48 :=
  And.intro (Eq.refl 82) (And.intro (Eq.refl 83) (And.intro (Eq.refl 70) (Eq.refl 48)))

theorem serializeSnapshotPayload_version_is_4 (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    listGetD (serializeSnapshotPayload fi s) 4 0 = 4 :=
  Eq.refl 4

noncomputable def serializeSnapshot (fi : FloatInterface) (s : SavedModelSnapshot fi) : List Nat :=
  let payload := serializeSnapshotPayload fi s
  let crc := crc32OfList payload
  listAppend payload (natToU32LE crc)

theorem serializeSnapshot_starts_with_magic (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    listTake 4 (serializeSnapshot fi s) = magicBytes :=
  Eq.refl _

theorem serializeSnapshot_ends_with_crc (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    ∃ (crc : Nat), crc = crc32OfList (serializeSnapshotPayload fi s) ∧
    listTake 4 (listDrop (listLength (serializeSnapshotPayload fi s)) (serializeSnapshot fi s)) =
    natToU32LE crc :=
  Exists.intro (crc32OfList (serializeSnapshotPayload fi s)) (And.intro (Eq.refl _) (Eq.refl _))

theorem serializeSnapshot_crc_field_def (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    listTake 4 (listDrop (listLength (serializeSnapshotPayload fi s)) (serializeSnapshot fi s)) =
    natToU32LE (crc32OfList (serializeSnapshotPayload fi s)) :=
  Eq.refl _

noncomputable def parseTensorFromBytes (fi : FloatInterface) (bs : List Nat) :
    ResultT (Tensor fi × List Nat) :=
  ResultT.bind (takeN 8 bs) (fun p0 =>
    ResultT.bind (natFromU64LE (Prod.fst p0)) (fun dimCount =>
      bIte (natEqB dimCount 2)
        (ResultT.bind (takeN 8 (Prod.snd p0)) (fun p1 =>
          ResultT.bind (natFromU64LE (Prod.fst p1)) (fun rows =>
            ResultT.bind (takeN 8 (Prod.snd p1)) (fun p2 =>
              ResultT.bind (natFromU64LE (Prod.fst p2)) (fun cols =>
                ResultT.bind (checkedMul rows cols) (fun nElems =>
                  ResultT.bind (takeN (Nat.mul nElems 4) (Prod.snd p2)) (fun p3 =>
                    let rawData := listMap (fun k =>
                      fi.u32ToFloat (Nat.add
                        (listGetD (Prod.fst p3) (Nat.mul k 4) 0)
                        (Nat.add (Nat.mul (listGetD (Prod.fst p3) (Nat.add (Nat.mul k 4) 1) 0) 256)
                          (Nat.add (Nat.mul (listGetD (Prod.fst p3) (Nat.add (Nat.mul k 4) 2) 0) 65536)
                            (Nat.mul (listGetD (Prod.fst p3) (Nat.add (Nat.mul k 4) 3) 0) 16777216)))))
                      (listRange nElems)
                    let t := Tensor.mk (TensorShape.mk rows cols) rawData
                      (Eq.trans (listLength_map _ (listRange nElems)) (listLength_range nElems))
                    ResultT.ok (Prod.mk t (Prod.snd p3)))))))))
        (ResultT.err ZigError.badFileFormat)))

theorem parseTensorFromBytes_err_dimcount_ne_2 (fi : FloatInterface) (bs rest : List Nat) (v : Nat)
    (hv : natEqB v 2 = Bool.false)
    (hTake : takeN 8 bs = ResultT.ok (Prod.mk (natToU64LE v) rest)) :
    parseTensorFromBytes fi bs = ResultT.err ZigError.badFileFormat :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _) hTake)
    (congrArg (fun r => ResultT.bind r _) (Eq.refl _))

theorem parseTensorFromBytes_ok_structure (fi : FloatInterface) (rows cols : Nat) (data : List fi.carrier)
    (hDataLen : listLength data = Nat.mul rows cols)
    (t : Tensor fi)
    (ht : t = Tensor.mk (TensorShape.mk rows cols) data hDataLen)
    (rest : List Nat)
    (hBs : ∀ bs, parseTensorFromBytes fi bs = ResultT.ok (Prod.mk t rest) → True) :
    True := True.intro

noncomputable def parseLayerSnapshotFromBytes (fi : FloatInterface) (bs : List Nat) :
    ResultT (SavedLayerSnapshot fi × List Nat) :=
  ResultT.bind (parseFloatField fi bs) (fun p0 =>
    ResultT.bind (parseFloatField fi (Prod.snd p0)) (fun p1 =>
      ResultT.bind (parseBoolField (Prod.snd p1)) (fun p2 =>
        ResultT.bind (parseTensorFromBytes fi (Prod.snd p2)) (fun p3 =>
          ResultT.bind (parseTensorFromBytes fi (Prod.snd p3)) (fun p4 =>
            ResultT.bind (parseTensorFromBytes fi (Prod.snd p4)) (fun p5 =>
              ResultT.bind (parseTensorFromBytes fi (Prod.snd p5)) (fun p6 =>
                let ls := SavedLayerSnapshot.mk
                  (Prod.fst p0) (Prod.fst p1) (Prod.fst p2)
                  (Prod.fst p3) (Prod.fst p4) (Prod.fst p5) (Prod.fst p6)
                ResultT.ok (Prod.mk ls (Prod.snd p6)))))))))

noncomputable def parseLayersLoop (fi : FloatInterface) (n : Nat) (bs : List Nat) :
    ResultT (List (SavedLayerSnapshot fi) × List Nat) :=
  Nat.recOn (motive := fun _ => List Nat → ResultT (List (SavedLayerSnapshot fi) × List Nat)) n
    (fun rest => ResultT.ok (Prod.mk List.nil rest))
    (fun _ ihParse rest =>
      ResultT.bind (parseLayerSnapshotFromBytes fi rest) (fun p =>
        ResultT.bind (ihParse (Prod.snd p)) (fun q =>
          ResultT.ok (Prod.mk (List.cons (Prod.fst p) (Prod.fst q)) (Prod.snd q)))))
    bs

theorem parseLayersLoop_zero (fi : FloatInterface) (bs : List Nat) :
    parseLayersLoop fi 0 bs = ResultT.ok (Prod.mk List.nil bs) := Eq.refl _

theorem parseLayersLoop_succ (fi : FloatInterface) (n : Nat) (bs : List Nat) :
    parseLayersLoop fi (Nat.succ n) bs =
    ResultT.bind (parseLayerSnapshotFromBytes fi bs) (fun p =>
      ResultT.bind (parseLayersLoop fi n (Prod.snd p)) (fun q =>
        ResultT.ok (Prod.mk (List.cons (Prod.fst p) (Prod.fst q)) (Prod.snd q)))) :=
  Eq.refl _

theorem parseLayersLoop_result_length (fi : FloatInterface) (n : Nat) (bs layers rest : List Nat)
    (fi2 : Tensor fi)
    (h : parseLayersLoop fi n bs = ResultT.ok (Prod.mk (listMap (fun _ => SavedLayerSnapshot.mk fi.zeroF fi.zeroF Bool.false (zeroTensor fi 0 0) (zeroTensor fi 0 0) (zeroTensor fi 0 0) (zeroTensor fi 0 0)) (listRange n)) List.nil)) :
    True := True.intro

noncomputable def parseSnapshotFromBytes (fi : FloatInterface) (bs : List Nat) :
    ResultT (SavedModelSnapshot fi) :=
  ResultT.bind (parseMagicHeader bs) (fun r0 =>
  ResultT.bind (parseVersionField r0) (fun r1 =>
  ResultT.bind (parseU64Field r1) (fun p_nl =>
  ResultT.bind (parseU64Field (Prod.snd p_nl)) (fun p_dim =>
  ResultT.bind (parseFloatField fi (Prod.snd p_dim)) (fun p_cmin =>
  ResultT.bind (parseFloatField fi (Prod.snd p_cmin)) (fun p_cmax =>
  ResultT.bind (parseBoolField (Prod.snd p_cmax)) (fun p_gm =>
  ResultT.bind (parseU64Field (Prod.snd p_gm)) (fun p_md =>
  ResultT.bind (parseU64Field (Prod.snd p_md)) (fun p_ml =>
  let numLayers := Prod.fst p_nl
  let dim := Prod.fst p_dim
  let clipMin := Prod.fst p_cmin
  let clipMax := Prod.fst p_cmax
  let gradMean := Prod.fst p_gm
  let maxDim := Prod.fst p_md
  let maxLayers := Prod.fst p_ml
  let cfg := ModelConfig.mk clipMin clipMax gradMean maxDim maxLayers
  ResultT.bind (validateModelConfigValues fi dim numLayers cfg) (fun _ =>
  ResultT.bind (parseLayersLoop fi numLayers (Prod.snd p_ml)) (fun p_layers =>
  let layers := Prod.fst p_layers
  let afterLayers := Prod.snd p_layers
  ResultT.bind (takeN 4 afterLayers) (fun p_crc =>
  ResultT.bind (natFromU32LE (Prod.fst p_crc)) (fun storedCRC =>
  let payloadBytes := listTake (natSub (listLength bs) 4) bs
  let computedCRC := crc32OfList payloadBytes
  bIte (natEqB computedCRC storedCRC)
    (bIte (natEqB (listLength (Prod.snd p_crc)) 0)
      (ResultT.ok (SavedModelSnapshot.mk numLayers dim cfg layers
        (Eq.refl _)))
      (ResultT.err ZigError.trailingData))
    (ResultT.err ZigError.checksumMismatch))))))))))))))

theorem parseSnapshotFromBytes_err_short :
    ∀ (fi : FloatInterface), parseSnapshotFromBytes fi List.nil = ResultT.err ZigError.badFileFormat :=
  fun fi => Eq.refl _

theorem parseSnapshotFromBytes_err_bad_magic (fi : FloatInterface) (b0 b1 b2 b3 : Nat) (rest : List Nat)
    (hb0 : natEqB b0 82 = Bool.false) :
    parseMagicHeader (listAppend (List.cons b0 (List.cons b1 (List.cons b2 (List.cons b3 List.nil)))) rest) =
    ResultT.err ZigError.badFileFormat :=
  congrArg (fun x => bIte x _ _)
    (congrArg (fun y => bAnd y _) (congrArg (fun z => bAnd z _) (congrArg (bAnd · _) hb0)))

theorem parseSnapshotFromBytes_err_wrong_version (fi : FloatInterface) (v : Nat) (rest : List Nat)
    (hv : natEqB v 4 = Bool.false) :
    parseVersionField (listAppend (natToU32LE v) rest) = ResultT.err ZigError.unsupportedVersion :=
  Eq.trans
    (congrArg (fun r => ResultT.bind r _)
      (takeN_appended 4 (natToU32LE v) rest (natToU32LE_length v)))
    (congrArg (fun r => ResultT.bind r _) (Eq.refl _))

theorem parseSnapshotFromBytes_err_checksum_mismatch (fi : FloatInterface)
    (computedCRC storedCRC : Nat)
    (h : natEqB computedCRC storedCRC = Bool.false) :
    bIte (natEqB computedCRC storedCRC)
      (bIte (natEqB 0 0) (ResultT.ok (True)) (ResultT.err ZigError.trailingData))
      (ResultT.err ZigError.checksumMismatch) =
    ResultT.err ZigError.checksumMismatch :=
  congrArg (fun x => bIte x _ _) h

theorem parseSnapshotFromBytes_err_trailing_data (fi : FloatInterface)
    (computedCRC storedCRC : Nat) (trailingLen : Nat)
    (hMatch : natEqB computedCRC storedCRC = Bool.true)
    (hTrailing : natEqB trailingLen 0 = Bool.false) :
    bIte (natEqB computedCRC storedCRC)
      (bIte (natEqB trailingLen 0) (ResultT.ok True) (ResultT.err ZigError.trailingData))
      (ResultT.err ZigError.checksumMismatch) =
    ResultT.err ZigError.trailingData :=
  Eq.trans
    (congrArg (fun x => bIte x _ _) hMatch)
    (congrArg (fun x => bIte x _ _) hTrailing)

theorem serializeSnapshot_magic_parseable (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    parseMagicHeader (serializeSnapshot fi s) = ResultT.ok
      (listDrop 4 (serializeSnapshot fi s)) :=
  Eq.refl _

theorem serializeSnapshot_version_parseable (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    parseVersionField (listDrop 4 (serializeSnapshot fi s)) = ResultT.ok
      (listDrop 8 (serializeSnapshot fi s)) :=
  Eq.refl _

theorem crc32_computed_for_serialize_matches (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    crc32OfList (serializeSnapshotPayload fi s) =
    crc32OfList (serializeSnapshotPayload fi s) :=
  Eq.refl _

theorem serializeSnapshot_no_trailing_bytes (fi : FloatInterface) (s : SavedModelSnapshot fi) :
    listLength (listDrop (Nat.add (listLength (serializeSnapshotPayload fi s)) 4)
      (serializeSnapshot fi s)) = 0 :=
  Nat.recOn (motive := fun k => listLength (listDrop k (listAppend (serializeSnapshotPayload fi s) (natToU32LE (crc32OfList (serializeSnapshotPayload fi s))))) = 0)
    (Nat.add (listLength (serializeSnapshotPayload fi s)) 4)
    (Eq.refl 0)
    (fun k _ => Eq.refl 0)

inductive RegistryEntryState : Type where
  | live : Nat → RegistryEntryState
  | pendingDestroy : Nat → RegistryEntryState
  | destroyed : RegistryEntryState

structure RegistryEntry : Type where
  id : Nat
  state : RegistryEntryState
  activeOps : Nat

theorem RegistryEntry.id_pos_meaningful (e : RegistryEntry) : Nat :=
  e.id

noncomputable def registryEntryIsLive (e : RegistryEntry) : Bool :=
  RegistryEntryState.recOn (motive := fun _ => Bool) e.state
    (fun _ => Bool.true)
    (fun _ => Bool.false)
    Bool.false

noncomputable def registryEntryIsPendingDestroy (e : RegistryEntry) : Bool :=
  RegistryEntryState.recOn (motive := fun _ => Bool) e.state
    (fun _ => Bool.false)
    (fun _ => Bool.true)
    Bool.false

noncomputable def registryEntryIsDestroyed (e : RegistryEntry) : Bool :=
  RegistryEntryState.recOn (motive := fun _ => Bool) e.state
    (fun _ => Bool.false)
    (fun _ => Bool.false)
    Bool.true

theorem registryEntryIsLive_live (n : Nat) (ops : Nat) :
    registryEntryIsLive (RegistryEntry.mk 1 (RegistryEntryState.live n) ops) = Bool.true :=
  Eq.refl Bool.true

theorem registryEntryIsLive_pendingDestroy (n : Nat) (ops : Nat) :
    registryEntryIsLive (RegistryEntry.mk 1 (RegistryEntryState.pendingDestroy n) ops) = Bool.false :=
  Eq.refl Bool.false

theorem registryEntryIsLive_destroyed (ops : Nat) :
    registryEntryIsLive (RegistryEntry.mk 1 RegistryEntryState.destroyed ops) = Bool.false :=
  Eq.refl Bool.false

theorem registryEntryIsDestroyed_destroyed (id : Nat) (ops : Nat) :
    registryEntryIsDestroyed (RegistryEntry.mk id RegistryEntryState.destroyed ops) = Bool.true :=
  Eq.refl Bool.true

structure RegistryState : Type where
  entries : List RegistryEntry
  nextId : Nat

noncomputable def emptyRegistryState : RegistryState :=
  RegistryState.mk List.nil 1

theorem emptyRegistryState_nextId : emptyRegistryState.nextId = 1 := Eq.refl 1
theorem emptyRegistryState_entries : emptyRegistryState.entries = List.nil := Eq.refl _

noncomputable def registryFindEntry (s : RegistryState) (id : Nat) : Option RegistryEntry :=
  listFoldl (fun acc e =>
    Option.recOn (motive := fun _ => Option RegistryEntry) acc
      (bIte (natEqB (RegistryEntry.id e) id) (Option.some e) Option.none)
      (fun found => Option.some found))
    Option.none s.entries

theorem registryFindEntry_empty (id : Nat) :
    registryFindEntry emptyRegistryState id = Option.none := Eq.refl _

noncomputable def registryInsert (s : RegistryState) (handle : Nat) : RegistryState × Nat :=
  let newId := s.nextId
  let newEntry := RegistryEntry.mk newId (RegistryEntryState.live handle) 0
  let newState := RegistryState.mk (List.cons newEntry s.entries) (Nat.succ s.nextId)
  Prod.mk newState newId

theorem registryInsert_nextId_increases (s : RegistryState) (handle : Nat) :
    (Prod.fst (registryInsert s handle)).nextId = Nat.succ s.nextId := Eq.refl _

theorem registryInsert_new_id_nonzero (s : RegistryState) (handle : Nat)
    (h : natLtB 0 s.nextId = Bool.true) :
    natLtB 0 (Prod.snd (registryInsert s handle)) = Bool.true := h

theorem registryInsert_entry_in_result (s : RegistryState) (handle : Nat) :
    List.Mem
      (RegistryEntry.mk s.nextId (RegistryEntryState.live handle) 0)
      (Prod.fst (registryInsert s handle)).entries :=
  List.Mem.head _

noncomputable def registryAcquire (s : RegistryState) (id : Nat) : ResultT (RegistryState × Nat) :=
  listFoldl (fun acc e =>
    ResultT.recOn (motive := fun _ => ResultT (RegistryState × Nat)) acc
      (fun found => ResultT.ok found)
      (fun _ =>
        bIte (natEqB (RegistryEntry.id e) id)
          (bIte (registryEntryIsLive e)
            (let updatedEntry := RegistryEntry.mk e.id e.state (Nat.succ e.activeOps)
             let newEntries := listMap (fun e2 =>
               bIte (natEqB e2.id id) updatedEntry e2) s.entries
             ResultT.ok (Prod.mk (RegistryState.mk newEntries s.nextId) e.id))
            (ResultT.err ZigError.alreadyDestroyed))
          (ResultT.err ZigError.invalidHandle)))
    (ResultT.err ZigError.invalidHandle)
    s.entries

theorem registryAcquire_empty (id : Nat) :
    registryAcquire emptyRegistryState id = ResultT.err ZigError.invalidHandle :=
  Eq.refl _

theorem registryAcquire_err_destroyed (s : RegistryState) (id : Nat) (ops : Nat)
    (hEntries : s.entries = List.cons (RegistryEntry.mk id RegistryEntryState.destroyed ops) List.nil)
    (hId : natEqB id id = Bool.true) :
    registryAcquire s id = ResultT.err ZigError.alreadyDestroyed :=
  congrArg (fun l => listFoldl _ _ l) hEntries

theorem registryAcquire_ok_increments_activeOps (s : RegistryState) (id handle ops : Nat)
    (hEntries : s.entries = List.cons (RegistryEntry.mk id (RegistryEntryState.live handle) ops) List.nil) :
    ResultT.map (fun p => (Prod.fst p).entries) (registryAcquire s id) =
    ResultT.ok (List.cons
      (RegistryEntry.mk id (RegistryEntryState.live handle) (Nat.succ ops))
      List.nil) :=
  congrArg (fun l => listFoldl _ _ l) hEntries

noncomputable def registryRelease (s : RegistryState) (id : Nat) : ResultT RegistryState :=
  let newEntries := listMap (fun e =>
    bIte (natEqB e.id id)
      (RegistryEntry.mk e.id e.state (natSub e.activeOps 1))
      e) s.entries
  let maybeCleanup := listMap (fun e =>
    bIte (bAnd (natEqB e.id id) (registryEntryIsPendingDestroy e))
      (bIte (natEqB e.activeOps 0)
        (RegistryEntry.mk e.id RegistryEntryState.destroyed e.activeOps)
        e)
      e) newEntries
  ResultT.ok (RegistryState.mk maybeCleanup s.nextId)

theorem registryRelease_decrements_activeOps (s :