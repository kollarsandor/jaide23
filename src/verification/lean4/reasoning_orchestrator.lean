import Std

inductive Cmp where
  | lt
  | eq
  | gt
deriving Repr, DecidableEq

inductive RunResult (ε σ α : Type) where
  | ok : σ → α → RunResult ε σ α
  | err : σ → ε → RunResult ε σ α
deriving Repr

inductive StoreState where
  | live
  | freed
deriving Repr, DecidableEq

structure Store where
  state : StoreState
  cap : Nat
deriving Repr

def Store.valid (s : Store) : Prop := True

inductive OrchestratorError where
  | allocationFailure
  | symmetryDetectionFailure
  | chaosKernelExecutionFailure
  | graphMutationFailure
  | invalidNumericPrecondition
  | phaseIdOverflow
  | appendAfterFree
deriving Repr, DecidableEq

structure NumSem where
  α : Type
  zero : α
  one : α
  two : α
  three : α
  half : α
  cent : α
  tenth : α
  oneMillion : α
  oneMicro : α
  oneHundredth : α
  positiveInfinity : α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  abs : α → α
  max : α → α → α
  sqrt : α → α
  cos : α → α
  clamp : α → α → α → α
  ofNat : Nat → α
  finite : α → Prop
  le : α → α → Prop
  lt : α → α → Prop
  eqv : α → α → Prop
  abs_nonneg : ∀ x, le zero (abs x)
  max_left : ∀ x y, le x (max x y)
  max_right : ∀ x y, le y (max x y)
  one_pos : lt zero one
  denom_pos : ∀ x, lt zero (max (abs x) one)
  div_pos_wf : ∀ x d, lt zero d → finite x → finite d → finite (div x d)
  sqrt_nonneg : ∀ x, le zero (sqrt x)
  mag_zero_law : sqrt zero = zero
  clamp_low : ∀ x lo hi, le lo hi → le lo (clamp x lo hi)
  clamp_high : ∀ x lo hi, le lo hi → le (clamp x lo hi) hi
  clamp_id : ∀ x lo hi, le lo x → le x hi → clamp x lo hi = x
  finite_zero : finite zero
  finite_one : finite one
  finite_two : finite two
  finite_three : finite three
  finite_half : finite half
  finite_cent : finite cent
  finite_tenth : finite tenth
  finite_oneMillion : finite oneMillion
  finite_oneMicro : finite oneMicro
  finite_oneHundredth : finite oneHundredth
  finite_add : ∀ x y, finite x → finite y → finite (add x y)
  finite_sub : ∀ x y, finite x → finite y → finite (sub x y)
  finite_mul : ∀ x y, finite x → finite y → finite (mul x y)
  finite_abs : ∀ x, finite x → finite (abs x)
  finite_max : ∀ x y, finite x → finite y → finite (max x y)
  finite_sqrt : ∀ x, finite x → finite (sqrt x)
  finite_cos : ∀ x, finite x → finite (cos x)
  finite_clamp : ∀ x lo hi, finite x → finite lo → finite hi → finite (clamp x lo hi)

namespace NumSem

variable (N : NumSem)

def absDiff (x y : N.α) : N.α := N.abs (N.sub x y)
def relDeltaDenom (x : N.α) : N.α := N.max (N.abs x) N.one
def converges (current previous threshold : N.α) : Prop :=
  N.lt (N.div (absDiff N current previous) (relDeltaDenom N previous)) threshold
def minStyle (x y z : N.α) : Prop :=
  z = x ∧ N.le z y ∨ z = y ∧ N.le z x

theorem relDeltaDenom_positive (x : N.α) : N.lt N.zero (relDeltaDenom N x) :=
  N.denom_pos x

theorem convergence_bound {c p t : N.α} (h : converges N c p t) :
    N.lt (N.div (absDiff N c p) (relDeltaDenom N p)) t := h

theorem convergence_intro {c p t : N.α}
    (h : N.lt (N.div (absDiff N c p) (relDeltaDenom N p)) t) :
    converges N c p t := h

theorem clamp01_low (x : N.α) (h01 : N.le N.zero N.one) :
    N.le N.zero (N.clamp x N.zero N.one) :=
  N.clamp_low x N.zero N.one h01

theorem clamp01_high (x : N.α) (h01 : N.le N.zero N.one) :
    N.le (N.clamp x N.zero N.one) N.one :=
  N.clamp_high x N.zero N.one h01

theorem clamp13_low (x : N.α) (h13 : N.le N.one N.three) :
    N.le N.one (N.clamp x N.one N.three) :=
  N.clamp_low x N.one N.three h13

theorem clamp13_high (x : N.α) (h13 : N.le N.one N.three) :
    N.le (N.clamp x N.one N.three) N.three :=
  N.clamp_high x N.one N.three h13

theorem clamp_id_range {x lo hi : N.α} (hlo : N.le lo x) (hhi : N.le x hi) :
    N.clamp x lo hi = x :=
  N.clamp_id x lo hi hlo hhi

end NumSem

abbrev U8 := Fin 256

abbrev PatternId := Fin 32 → U8

def PatternId.zero : PatternId := fun _ => ⟨0, Nat.succ_pos 255⟩

theorem PatternId.fixed_size (p : PatternId) : (Fin 32 → U8) = PatternId := rfl

inductive ThoughtLevel where
  | local
  | global
  | meta
deriving Repr, DecidableEq

def ThoughtLevel.code : ThoughtLevel → Fin 3
  | ThoughtLevel.local => ⟨0, Nat.succ_pos 2⟩
  | ThoughtLevel.global => ⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩
  | ThoughtLevel.meta => ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩

def ThoughtLevel.toText : ThoughtLevel → String
  | ThoughtLevel.local => "local"
  | ThoughtLevel.global => "global"
  | ThoughtLevel.meta => "meta"

theorem ThoughtLevel.exhaustive (t : ThoughtLevel) :
    t = ThoughtLevel.local ∨ t = ThoughtLevel.global ∨ t = ThoughtLevel.meta :=
  match t with
  | ThoughtLevel.local => Or.inl rfl
  | ThoughtLevel.global => Or.inr (Or.inl rfl)
  | ThoughtLevel.meta => Or.inr (Or.inr rfl)

theorem ThoughtLevel.local_text : ThoughtLevel.toText ThoughtLevel.local = "local" := rfl
theorem ThoughtLevel.global_text : ThoughtLevel.toText ThoughtLevel.global = "global" := rfl
theorem ThoughtLevel.meta_text : ThoughtLevel.toText ThoughtLevel.meta = "meta" := rfl

structure Cx (N : NumSem) where
  re : N.α
  im : N.α
deriving Repr

namespace Cx

def valid {N : NumSem} (z : Cx N) : Prop := N.finite z.re ∧ N.finite z.im
def mag {N : NumSem} (z : Cx N) : N.α :=
  N.sqrt (N.add (N.mul z.re z.re) (N.mul z.im z.im))
def shift {N : NumSem} (z : Cx N) (dr di : N.α) : Cx N :=
  { re := N.add z.re dr, im := N.add z.im di }

theorem mag_nonneg {N : NumSem} (z : Cx N) : N.le N.zero (mag z) :=
  N.sqrt_nonneg (N.add (N.mul z.re z.re) (N.mul z.im z.im))

theorem mag_zero {N : NumSem} : mag ({ re := N.zero, im := N.zero } : Cx N) =
    N.sqrt (N.add (N.mul N.zero N.zero) (N.mul N.zero N.zero)) := rfl

theorem shift_valid {N : NumSem} {z : Cx N} {dr di : N.α}
    (hz : valid z) (hdr : N.finite dr) (hdi : N.finite di) : valid (shift z dr di) :=
  And.intro (N.finite_add z.re dr hz.left hdr) (N.finite_add z.im di hz.right hdi)

theorem energy_part_valid {N : NumSem} {z : Cx N} (hz : valid z) :
    N.finite (mag z) :=
  N.finite_sqrt (N.add (N.mul z.re z.re) (N.mul z.im z.im))
    (N.finite_add (N.mul z.re z.re) (N.mul z.im z.im)
      (N.finite_mul z.re z.re hz.left hz.left)
      (N.finite_mul z.im z.im hz.right hz.right))

end Cx

structure Qubit (N : NumSem) where
  a : Cx N
deriving Repr

namespace Qubit

def valid {N : NumSem} (q : Qubit N) : Prop := Cx.valid q.a
def basis0 {N : NumSem} : Qubit N := { a := { re := N.one, im := N.zero } }
def basis1 {N : NumSem} : Qubit N := { a := { re := N.zero, im := N.one } }
def perturb {N : NumSem} (q : Qubit N) (p : N.α) : Qubit N :=
  { a := { re := N.add q.a.re (N.mul p N.cent), im := N.add q.a.im (N.mul p N.cent) } }

theorem basis0_valid {N : NumSem} : valid (basis0 : Qubit N) :=
  And.intro N.finite_one N.finite_zero

theorem basis1_valid {N : NumSem} : valid (basis1 : Qubit N) :=
  And.intro N.finite_zero N.finite_one

theorem perturb_valid {N : NumSem} {q : Qubit N} {p : N.α}
    (hq : valid q) (hp : N.finite p) : valid (perturb q p) :=
  And.intro
    (N.finite_add q.a.re (N.mul p N.cent) hq.left (N.finite_mul p N.cent hp N.finite_cent))
    (N.finite_add q.a.im (N.mul p N.cent) hq.right (N.finite_mul p N.cent hp N.finite_cent))

end Qubit

structure Node (N : NumSem) where
  ident : String
  data : String
  qubit : Qubit N
  phase : N.α
deriving Repr

namespace Node

def valid {N : NumSem} (n : Node N) : Prop := Qubit.valid n.qubit ∧ N.finite n.phase
def init {N : NumSem} (ident data : String) (q : Qubit N) (phase : N.α) : Node N :=
  { ident := ident, data := data, qubit := q, phase := phase }
theorem init_valid {N : NumSem} {i d : String} {q : Qubit N} {p : N.α}
    (hq : Qubit.valid q) (hp : N.finite p) : valid (init i d q p) :=
  And.intro hq hp
def setPhase {N : NumSem} (n : Node N) (p : N.α) : Node N :=
  { n with phase := p }
theorem setPhase_valid {N : NumSem} {n : Node N} {p : N.α}
    (hn : valid n) (hp : N.finite p) : valid (setPhase n p) :=
  And.intro hn.left hp

end Node

structure Edge (N : NumSem) where
  weight : N.α
  fractal_dimension : N.α
  quantum_correlation : Cx N
deriving Repr

namespace Edge

def valid {N : NumSem} (e : Edge N) : Prop :=
  N.finite e.weight ∧ N.finite e.fractal_dimension ∧ Cx.valid e.quantum_correlation
def strongValid {N : NumSem} (e : Edge N) : Prop :=
  valid e ∧ N.le N.zero e.weight ∧ N.le e.weight N.one ∧
  N.le N.one e.fractal_dimension ∧ N.le e.fractal_dimension N.three
def localPerturb {N : NumSem} (e : Edge N) (delta : N.α) : Edge N :=
  let w := N.clamp (N.add e.weight delta) N.zero N.one
  let cd := N.mul delta N.tenth
  { weight := w,
    fractal_dimension := e.fractal_dimension,
    quantum_correlation :=
      { re := N.add e.quantum_correlation.re cd,
        im := N.add e.quantum_correlation.im (N.mul cd N.half) } }
def rebalance {N : NumSem} (e : Edge N) (avg : N.α) : Edge N :=
  let adjustment := N.mul (N.sub avg e.fractal_dimension) N.tenth
  { e with fractal_dimension := N.clamp (N.add e.fractal_dimension adjustment) N.one N.three }

theorem local_weight_low {N : NumSem} (e : Edge N) (d : N.α) (h : N.le N.zero N.one) :
    N.le N.zero (localPerturb e d).weight :=
  N.clamp_low (N.add e.weight d) N.zero N.one h

theorem local_weight_high {N : NumSem} (e : Edge N) (d : N.α) (h : N.le N.zero N.one) :
    N.le (localPerturb e d).weight N.one :=
  N.clamp_high (N.add e.weight d) N.zero N.one h

theorem rebalance_low {N : NumSem} (e : Edge N) (avg : N.α) (h : N.le N.one N.three) :
    N.le N.one (rebalance e avg).fractal_dimension :=
  N.clamp_low (N.add e.fractal_dimension (N.mul (N.sub avg e.fractal_dimension) N.tenth)) N.one N.three h

theorem rebalance_high {N : NumSem} (e : Edge N) (avg : N.α) (h : N.le N.one N.three) :
    N.le (rebalance e avg).fractal_dimension N.three :=
  N.clamp_high (N.add e.fractal_dimension (N.mul (N.sub avg e.fractal_dimension) N.tenth)) N.one N.three h

theorem local_corr_formula {N : NumSem} (e : Edge N) (d : N.α) :
    (localPerturb e d).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul d N.tenth) := rfl

theorem rebalance_formula {N : NumSem} (e : Edge N) (avg : N.α) :
    (rebalance e avg).fractal_dimension =
      N.clamp (N.add e.fractal_dimension (N.mul (N.sub avg e.fractal_dimension) N.tenth)) N.one N.three := rfl

end Edge

structure EdgeEntry (N : NumSem) where
  key : String
  items : List (Edge N)
deriving Repr

structure Graph (N : NumSem) where
  nodes : List (Node N)
  edges : List (EdgeEntry N)
deriving Repr

namespace Graph

def valid {N : NumSem} (g : Graph N) : Prop :=
  (∀ n, n ∈ g.nodes → Node.valid n) ∧
  (∀ ee, ee ∈ g.edges → ∀ e, e ∈ ee.items → Edge.valid e)
def init {N : NumSem} : Graph N := { nodes := [], edges := [] }
def addNode {N : NumSem} (g : Graph N) (n : Node N) : Graph N :=
  { g with nodes := g.nodes ++ [n] }
def nodeOrder {N : NumSem} (g : Graph N) : List (Node N) := g.nodes
def edgeOrder {N : NumSem} (g : Graph N) : List (EdgeEntry N) := g.edges
def nodeCount {N : NumSem} (g : Graph N) : Nat := g.nodes.length
def edgeCount {N : NumSem} (g : Graph N) : Nat :=
  (g.edges.map (fun ee => ee.items.length)).foldl Nat.add 0
def contributionCount {N : NumSem} (g : Graph N) : Nat := nodeCount g + edgeCount g

theorem init_valid {N : NumSem} : valid (init : Graph N) :=
  And.intro
    (fun n h => False.elim h)
    (fun ee h => False.elim h)

theorem addNode_nodes {N : NumSem} (g : Graph N) (n : Node N) :
    (addNode g n).nodes = g.nodes ++ [n] := rfl

theorem nodeOrder_len {N : NumSem} (g : Graph N) :
    (nodeOrder g).length = nodeCount g := rfl

theorem edgeOrder_len {N : NumSem} (g : Graph N) :
    (edgeOrder g).length = g.edges.length := rfl

theorem count_def {N : NumSem} (g : Graph N) :
    contributionCount g = nodeCount g + edgeCount g := rfl

end Graph

structure Prng (N : NumSem) where
  seed : Nat
deriving Repr

namespace Prng

def valid {N : NumSem} (p : Prng N) : Prop := True
def next {N : NumSem} (p : Prng N) : Prng N :=
  { seed := p.seed * 1664525 + 1013904223 }
def sample {N : NumSem} (p : Prng N) : Prng N × N.α := (next p, N.half)
def sampleIn01 {N : NumSem} (x : N.α) : Prop := N.le N.zero x ∧ N.le x N.one

theorem next_valid {N : NumSem} (p : Prng N) (h : valid p) : valid (next p) := True.intro

theorem sample_state_valid {N : NumSem} (p : Prng N) (h : valid p) : valid (sample p).fst := True.intro

def perturbValue {N : NumSem} (x : N.α) : N.α := N.mul (N.sub x N.half) N.tenth
def edgeDelta {N : NumSem} (x : N.α) : N.α := N.mul (N.sub x N.half) (N.mul N.tenth N.half)

theorem local_perturb_def {N : NumSem} (x : N.α) :
    perturbValue x = N.mul (N.sub x N.half) N.tenth := rfl

theorem edge_delta_def {N : NumSem} (x : N.α) :
    edgeDelta x = N.mul (N.sub x N.half) (N.mul N.tenth N.half) := rfl

end Prng

structure QuantumState (N : NumSem) where
  amplitude_real : N.α
  amplitude_imag : N.α
  phase : N.α
  entanglement_degree : N.α
deriving Repr

namespace QuantumState

def valid {N : NumSem} (q : QuantumState N) : Prop :=
  N.finite q.amplitude_real ∧ N.finite q.amplitude_imag ∧
  N.finite q.phase ∧ N.finite q.entanglement_degree

end QuantumState

structure SymmetryTransform (N : NumSem) where
  act : QuantumState N → QuantumState N
  preserves : ∀ q, QuantumState.valid q → QuantumState.valid (act q)

namespace SymmetryTransform

def identity {N : NumSem} : SymmetryTransform N :=
  { act := fun q => q, preserves := fun q h => h }

theorem apply_valid {N : NumSem} (t : SymmetryTransform N) {q : QuantumState N}
    (h : QuantumState.valid q) : QuantumState.valid (t.act q) :=
  t.preserves q h

end SymmetryTransform

structure Optimizer (N : NumSem) where
  prng : Prng N
  transforms : List (SymmetryTransform N)
  detection_ok : Bool
deriving Repr

namespace Optimizer

def valid {N : NumSem} (o : Optimizer N) : Prop :=
  Prng.valid o.prng ∧ ∀ t, t ∈ o.transforms → True
def initWithSeed {N : NumSem} (seed : Nat) : Optimizer N :=
  { prng := { seed := seed }, transforms := [SymmetryTransform.identity], detection_ok := true }
def random {N : NumSem} (o : Optimizer N) : Optimizer N × N.α :=
  let r := Prng.sample o.prng
  ({ o with prng := r.fst }, r.snd)

inductive DetectRel {N : NumSem} (o : Optimizer N) (g : Graph N) :
    RunResult OrchestratorError (Optimizer N) (List (SymmetryTransform N)) → Prop where
  | ok : o.detection_ok = true → DetectRel o g (RunResult.ok o o.transforms)
  | fail : o.detection_ok = false →
      DetectRel o g (RunResult.err o OrchestratorError.symmetryDetectionFailure)

theorem random_valid {N : NumSem} {o : Optimizer N}
    (h : valid o) : valid (random o).fst :=
  And.intro True.intro (fun t ht => True.intro)

theorem detect_ok_valid {N : NumSem} {o : Optimizer N} {g : Graph N}
    (h : valid o) (hok : o.detection_ok = true) :
    DetectRel o g (RunResult.ok o o.transforms) :=
  DetectRel.ok hok

theorem detect_error {N : NumSem} {o : Optimizer N} {g : Graph N}
    (h : o.detection_ok = false) :
    DetectRel o g (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  DetectRel.fail h

end Optimizer

structure ChaosKernel where
  cycles : Nat
  fail_at : Option Nat
deriving Repr

namespace ChaosKernel

def valid (k : ChaosKernel) : Prop := True
def init : ChaosKernel := { cycles := 0, fail_at := Option.none }

inductive ExecRel : ChaosKernel → RunResult OrchestratorError ChaosKernel Unit → Prop where
  | ok (k : ChaosKernel) :
      k.fail_at = Option.none →
      ExecRel k (RunResult.ok { k with cycles := k.cycles + 1 } ())
  | fail (k : ChaosKernel) (n : Nat) :
      k.fail_at = Option.some n →
      ExecRel k (RunResult.err k OrchestratorError.chaosKernelExecutionFailure)

theorem success_valid {k k' : ChaosKernel} {u : Unit}
    (h : ExecRel k (RunResult.ok k' u)) (hk : valid k) : valid k' :=
  True.intro

theorem failure_represented (k : ChaosKernel) (n : Nat) (h : k.fail_at = Option.some n) :
    ExecRel k (RunResult.err k OrchestratorError.chaosKernelExecutionFailure) :=
  ExecRel.fail k n h

def repeatRel : Nat → ChaosKernel → RunResult OrchestratorError ChaosKernel Unit → Prop
  | 0, k, r => r = RunResult.ok k ()
  | Nat.succ m, k, r =>
      ∃ k1, ExecRel k (RunResult.ok k1 ()) ∧ repeatRel m k1 r ∨
            ExecRel k (RunResult.err k OrchestratorError.chaosKernelExecutionFailure) ∧
            r = RunResult.err k OrchestratorError.chaosKernelExecutionFailure

theorem repeat_zero (k : ChaosKernel) :
    repeatRel 0 k (RunResult.ok k ()) := rfl

end ChaosKernel

structure Phase (N : NumSem) where
  phase_id : Nat
  level : ThoughtLevel
  inner_iterations : Nat
  outer_iterations : Nat
  target_energy : N.α
  current_energy : N.α
  previous_energy : N.α
  convergence_threshold : N.α
  phase_start_time : Int
  phase_end_time : Int
  pattern_captures : List PatternId
  store : Store
deriving Repr

namespace Phase

def valid {N : NumSem} (p : Phase N) : Prop :=
  N.finite p.target_energy ∧ N.finite p.current_energy ∧
  N.finite p.previous_energy ∧ N.finite p.convergence_threshold ∧
  Store.valid p.store
def finalized (p : Phase N) : Prop := p.phase_end_time > 0
def init {N : NumSem} (st : Store) (time : Int)
    (level : ThoughtLevel) (inner outer phase_id : Nat) : Phase N :=
  { phase_id := phase_id,
    level := level,
    inner_iterations := inner,
    outer_iterations := outer,
    target_energy := N.tenth,
    current_energy := N.oneMillion,
    previous_energy := N.oneMillion,
    convergence_threshold := N.oneMicro,
    phase_start_time := time,
    phase_end_time := 0,
    pattern_captures := [],
    store := st }
def deinit {N : NumSem} (p : Phase N) : Phase N :=
  { p with store := { p.store with state := StoreState.freed } }

inductive RecordPatternRel {N : NumSem} :
    Phase N → PatternId → RunResult OrchestratorError (Phase N) Unit → Prop where
  | ok (p : Phase N) (pid : PatternId) :
      p.store.state = StoreState.live →
      p.pattern_captures.length < p.store.cap →
      RecordPatternRel p pid
        (RunResult.ok { p with pattern_captures := p.pattern_captures ++ [pid] } ())
  | alloc (p : Phase N) (pid : PatternId) :
      p.store.state = StoreState.live →
      p.store.cap ≤ p.pattern_captures.length →
      RecordPatternRel p pid (RunResult.err p OrchestratorError.allocationFailure)
  | freed (p : Phase N) (pid : PatternId) :
      p.store.state = StoreState.freed →
      RecordPatternRel p pid (RunResult.err p OrchestratorError.appendAfterFree)

def hasConverged {N : NumSem} (p : Phase N) : Prop :=
  N.converges p.current_energy p.previous_energy p.convergence_threshold
def updateEnergy {N : NumSem} (p : Phase N) (e : N.α) : Phase N :=
  { p with previous_energy := p.current_energy, current_energy := e }
def finalize {N : NumSem} (p : Phase N) (time : Int) : Phase N :=
  { p with phase_end_time := time }

inductive DurationRel {N : NumSem} (p : Phase N) (now : Int) : Int → Prop where
  | done : p.phase_end_time > 0 →
      DurationRel p now (p.phase_end_time - p.phase_start_time)
  | live : p.phase_end_time ≤ 0 →
      DurationRel p now (now - p.phase_start_time)

theorem init_level {N : NumSem} (st : Store) (tm : Int) (l : ThoughtLevel) (i o id : Nat) :
    (init (N := N) st tm l i o id).level = l := rfl

theorem init_valid {N : NumSem} (st : Store) (tm : Int) (l : ThoughtLevel) (i o id : Nat) :
    valid (init (N := N) st tm l i o id) :=
  And.intro N.finite_tenth
    (And.intro N.finite_oneMillion
      (And.intro N.finite_oneMillion
        (And.intro N.finite_oneMicro True.intro)))

theorem deinit_freed {N : NumSem} (p : Phase N) :
    (deinit p).store.state = StoreState.freed := rfl

theorem record_success_length {N : NumSem} (p : Phase N) (pid : PatternId)
    (hl : p.store.state = StoreState.live) (hc : p.pattern_captures.length < p.store.cap) :
    RecordPatternRel p pid
      (RunResult.ok { p with pattern_captures := p.pattern_captures ++ [pid] } ()) :=
  RecordPatternRel.ok p pid hl hc

theorem record_allocation_error {N : NumSem} (p : Phase N) (pid : PatternId)
    (hl : p.store.state = StoreState.live) (hc : p.store.cap ≤ p.pattern_captures.length) :
    RecordPatternRel p pid (RunResult.err p OrchestratorError.allocationFailure) :=
  RecordPatternRel.alloc p pid hl hc

theorem record_after_free_error {N : NumSem} (p : Phase N) (pid : PatternId)
    (hf : p.store.state = StoreState.freed) :
    RecordPatternRel p pid (RunResult.err p OrchestratorError.appendAfterFree) :=
  RecordPatternRel.freed p pid hf

theorem update_prev {N : NumSem} (p : Phase N) (e : N.α) :
    (updateEnergy p e).previous_energy = p.current_energy := rfl

theorem update_curr {N : NumSem} (p : Phase N) (e : N.α) :
    (updateEnergy p e).current_energy = e := rfl

theorem finalize_end {N : NumSem} (p : Phase N) (t : Int) :
    (finalize p t).phase_end_time = t := rfl

theorem duration_finalized {N : NumSem} (p : Phase N) (now : Int) (h : p.phase_end_time > 0) :
    DurationRel p now (p.phase_end_time - p.phase_start_time) :=
  DurationRel.done h

theorem duration_live {N : NumSem} (p : Phase N) (now : Int) (h : p.phase_end_time ≤ 0) :
    DurationRel p now (now - p.phase_start_time) :=
  DurationRel.live h

end Phase

structure Stats (N : NumSem) where
  total_phases : Nat
  local_phases : Nat
  global_phases : Nat
  meta_phases : Nat
  total_inner_loops : Nat
  total_outer_loops : Nat
  average_convergence_time : N.α
  best_energy_achieved : N.α
  patterns_discovered : Nat
  orchestration_start_time : Int
deriving Repr

namespace Stats

def valid {N : NumSem} (s : Stats N) : Prop :=
  s.total_phases = s.local_phases + s.global_phases + s.meta_phases ∧
  N.finite s.average_convergence_time ∧
  (N.finite s.best_energy_achieved ∨ s.best_energy_achieved = N.positiveInfinity)
def init {N : NumSem} (time : Int) : Stats N :=
  { total_phases := 0,
    local_phases := 0,
    global_phases := 0,
    meta_phases := 0,
    total_inner_loops := 0,
    total_outer_loops := 0,
    average_convergence_time := N.zero,
    best_energy_achieved := N.positiveInfinity,
    patterns_discovered := 0,
    orchestration_start_time := time }
def incLevel : ThoughtLevel → Stats N → Stats N
  | ThoughtLevel.local, s => { s with local_phases := s.local_phases + 1 }
  | ThoughtLevel.global, s => { s with global_phases := s.global_phases + 1 }
  | ThoughtLevel.meta, s => { s with meta_phases := s.meta_phases + 1 }
def recordPhase {N : NumSem} (s : Stats N) (p : Phase N) (duration : N.α) (newBest : N.α) : Stats N :=
  let n := s.total_phases + 1
  let s1 := incLevel p.level { s with total_phases := n }
  { s1 with
    total_inner_loops := s.total_inner_loops + p.inner_iterations,
    total_outer_loops := s.total_outer_loops + p.outer_iterations,
    best_energy_achieved := newBest,
    patterns_discovered := s.patterns_discovered + p.pattern_captures.length,
    average_convergence_time :=
      N.add s.average_convergence_time
        (N.div (N.sub duration s.average_convergence_time) (N.ofNat n)) }

theorem init_total {N : NumSem} (t : Int) :
    (init (N := N) t).total_phases = 0 := rfl

theorem init_valid {N : NumSem} (t : Int) :
    valid (init (N := N) t) :=
  And.intro rfl (And.intro N.finite_zero (Or.inr rfl))

theorem record_total {N : NumSem} (s : Stats N) (p : Phase N) (d nb : N.α) :
    (recordPhase s p d nb).total_phases = s.total_phases + 1 :=
  match p.level with
  | ThoughtLevel.local => rfl
  | ThoughtLevel.global => rfl
  | ThoughtLevel.meta => rfl

theorem record_patterns {N : NumSem} (s : Stats N) (p : Phase N) (d nb : N.α) :
    (recordPhase s p d nb).patterns_discovered =
      s.patterns_discovered + p.pattern_captures.length :=
  match p.level with
  | ThoughtLevel.local => rfl
  | ThoughtLevel.global => rfl
  | ThoughtLevel.meta => rfl

theorem record_average_formula {N : NumSem} (s : Stats N) (p : Phase N) (d nb : N.α) :
    (recordPhase s p d nb).average_convergence_time =
      N.add s.average_convergence_time
        (N.div (N.sub d s.average_convergence_time) (N.ofNat (s.total_phases + 1))) :=
  match p.level with
  | ThoughtLevel.local => rfl
  | ThoughtLevel.global => rfl
  | ThoughtLevel.meta => rfl

end Stats

structure Orch (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (Phase N)
  statistics : Stats N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace Orch

def historyValid {N : NumSem} (xs : List (Phase N)) : Prop :=
  ∀ p, p ∈ xs → Phase.valid p
def valid {N : NumSem} (o : Orch N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ Stats.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : Orch N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := Stats.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : Orch N) : Orch N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map Phase.deinit }
def setParameters {N : NumSem} (o : Orch N) (inner outer depth : Nat) : Orch N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : Orch N) (pn ue tn : Nat) : Orch N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Nat → Prop where
  | ok (o : Orch N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : Orch N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (Stats.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : Orch N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : Orch N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : Orch N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : Orch N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : Orch N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end Orch

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningPhase (N : NumSem) where
  phase_id : Nat
  level : ThoughtLevel
  inner_iterations : Nat
  outer_iterations : Nat
  target_energy : N.α
  current_energy : N.α
  previous_energy : N.α
  convergence_threshold : N.α
  phase_start_time : Int
  phase_end_time : Int
  pattern_captures : List PatternId
  store : Store
deriving Repr

namespace ReasoningPhase

def valid {N : NumSem} (p : ReasoningPhase N) : Prop :=
  N.finite p.target_energy ∧ N.finite p.current_energy ∧
  N.finite p.previous_energy ∧ N.finite p.convergence_threshold ∧
  Store.valid p.store
def finalized (p : ReasoningPhase N) : Prop := p.phase_end_time > 0
def init {N : NumSem} (st : Store) (time : Int)
    (level : ThoughtLevel) (inner outer phase_id : Nat) : ReasoningPhase N :=
  { phase_id := phase_id,
    level := level,
    inner_iterations := inner,
    outer_iterations := outer,
    target_energy := N.tenth,
    current_energy := N.oneMillion,
    previous_energy := N.oneMillion,
    convergence_threshold := N.oneMicro,
    phase_start_time := time,
    phase_end_time := 0,
    pattern_captures := [],
    store := st }
def deinit {N : NumSem} (p : ReasoningPhase N) : ReasoningPhase N :=
  { p with store := { p.store with state := StoreState.freed } }

inductive RecordPatternRel {N : NumSem} :
    ReasoningPhase N → PatternId → RunResult OrchestratorError (ReasoningPhase N) Unit → Prop where
  | ok (p : ReasoningPhase N) (pid : PatternId) :
      p.store.state = StoreState.live →
      p.pattern_captures.length < p.store.cap →
      RecordPatternRel p pid
        (RunResult.ok { p with pattern_captures := p.pattern_captures ++ [pid] } ())
  | alloc (p : ReasoningPhase N) (pid : PatternId) :
      p.store.state = StoreState.live →
      p.store.cap ≤ p.pattern_captures.length →
      RecordPatternRel p pid (RunResult.err p OrchestratorError.allocationFailure)
  | freed (p : ReasoningPhase N) (pid : PatternId) :
      p.store.state = StoreState.freed →
      RecordPatternRel p pid (RunResult.err p OrchestratorError.appendAfterFree)

def hasConverged {N : NumSem} (p : ReasoningPhase N) : Prop :=
  N.converges p.current_energy p.previous_energy p.convergence_threshold
def updateEnergy {N : NumSem} (p : ReasoningPhase N) (e : N.α) : ReasoningPhase N :=
  { p with previous_energy := p.current_energy, current_energy := e }
def finalize {N : NumSem} (p : ReasoningPhase N) (time : Int) : ReasoningPhase N :=
  { p with phase_end_time := time }

inductive DurationRel {N : NumSem} (p : ReasoningPhase N) (now : Int) : Int → Prop where
  | done : p.phase_end_time > 0 →
      DurationRel p now (p.phase_end_time - p.phase_start_time)
  | live : p.phase_end_time ≤ 0 →
      DurationRel p now (now - p.phase_start_time)

theorem init_level {N : NumSem} (st : Store) (tm : Int) (l : ThoughtLevel) (i o id : Nat) :
    (init (N := N) st tm l i o id).level = l := rfl

theorem init_valid {N : NumSem} (st : Store) (tm : Int) (l : ThoughtLevel) (i o id : Nat) :
    valid (init (N := N) st tm l i o id) :=
  And.intro N.finite_tenth
    (And.intro N.finite_oneMillion
      (And.intro N.finite_oneMillion
        (And.intro N.finite_oneMicro True.intro)))

theorem deinit_freed {N : NumSem} (p : ReasoningPhase N) :
    (deinit p).store.state = StoreState.freed := rfl

theorem record_success_length {N : NumSem} (p : ReasoningPhase N) (pid : PatternId)
    (hl : p.store.state = StoreState.live) (hc : p.pattern_captures.length < p.store.cap) :
    RecordPatternRel p pid
      (RunResult.ok { p with pattern_captures := p.pattern_captures ++ [pid] } ()) :=
  RecordPatternRel.ok p pid hl hc

theorem record_allocation_error {N : NumSem} (p : ReasoningPhase N) (pid : PatternId)
    (hl : p.store.state = StoreState.live) (hc : p.store.cap ≤ p.pattern_captures.length) :
    RecordPatternRel p pid (RunResult.err p OrchestratorError.allocationFailure) :=
  RecordPatternRel.alloc p pid hl hc

theorem record_after_free_error {N : NumSem} (p : ReasoningPhase N) (pid : PatternId)
    (hf : p.store.state = StoreState.freed) :
    RecordPatternRel p pid (RunResult.err p OrchestratorError.appendAfterFree) :=
  RecordPatternRel.freed p pid hf

theorem update_prev {N : NumSem} (p : ReasoningPhase N) (e : N.α) :
    (updateEnergy p e).previous_energy = p.current_energy := rfl

theorem update_curr {N : NumSem} (p : ReasoningPhase N) (e : N.α) :
    (updateEnergy p e).current_energy = e := rfl

theorem finalize_end {N : NumSem} (p : ReasoningPhase N) (t : Int) :
    (finalize p t).phase_end_time = t := rfl

theorem duration_finalized {N : NumSem} (p : ReasoningPhase N) (now : Int) (h : p.phase_end_time > 0) :
    DurationRel p now (p.phase_end_time - p.phase_start_time) :=
  DurationRel.done h

theorem duration_live {N : NumSem} (p : ReasoningPhase N) (now : Int) (h : p.phase_end_time ≤ 0) :
    DurationRel p now (now - p.phase_start_time) :=
  DurationRel.live h

end ReasoningPhase

structure OrchestratorStatistics (N : NumSem) where
  total_phases : Nat
  local_phases : Nat
  global_phases : Nat
  meta_phases : Nat
  total_inner_loops : Nat
  total_outer_loops : Nat
  average_convergence_time : N.α
  best_energy_achieved : N.α
  patterns_discovered : Nat
  orchestration_start_time : Int
deriving Repr

namespace OrchestratorStatistics

def valid {N : NumSem} (s : OrchestratorStatistics N) : Prop :=
  s.total_phases = s.local_phases + s.global_phases + s.meta_phases ∧
  N.finite s.average_convergence_time ∧
  (N.finite s.best_energy_achieved ∨ s.best_energy_achieved = N.positiveInfinity)
def init {N : NumSem} (time : Int) : OrchestratorStatistics N :=
  { total_phases := 0,
    local_phases := 0,
    global_phases := 0,
    meta_phases := 0,
    total_inner_loops := 0,
    total_outer_loops := 0,
    average_convergence_time := N.zero,
    best_energy_achieved := N.positiveInfinity,
    patterns_discovered := 0,
    orchestration_start_time := time }
def incLevel : ThoughtLevel → OrchestratorStatistics N → OrchestratorStatistics N
  | ThoughtLevel.local, s => { s with local_phases := s.local_phases + 1 }
  | ThoughtLevel.global, s => { s with global_phases := s.global_phases + 1 }
  | ThoughtLevel.meta, s => { s with meta_phases := s.meta_phases + 1 }
def recordPhase {N : NumSem} (s : OrchestratorStatistics N) (p : ReasoningPhase N) (duration : N.α) (newBest : N.α) : OrchestratorStatistics N :=
  let n := s.total_phases + 1
  let s1 := incLevel p.level { s with total_phases := n }
  { s1 with
    total_inner_loops := s.total_inner_loops + p.inner_iterations,
    total_outer_loops := s.total_outer_loops + p.outer_iterations,
    best_energy_achieved := newBest,
    patterns_discovered := s.patterns_discovered + p.pattern_captures.length,
    average_convergence_time :=
      N.add s.average_convergence_time
        (N.div (N.sub duration s.average_convergence_time) (N.ofNat n)) }

theorem init_total {N : NumSem} (t : Int) :
    (init (N := N) t).total_phases = 0 := rfl

theorem init_valid {N : NumSem} (t : Int) :
    valid (init (N := N) t) :=
  And.intro rfl (And.intro N.finite_zero (Or.inr rfl))

theorem record_total {N : NumSem} (s : OrchestratorStatistics N) (p : ReasoningPhase N) (d nb : N.α) :
    (recordPhase s p d nb).total_phases = s.total_phases + 1 :=
  match p.level with
  | ThoughtLevel.local => rfl
  | ThoughtLevel.global => rfl
  | ThoughtLevel.meta => rfl

theorem record_patterns {N : NumSem} (s : OrchestratorStatistics N) (p : ReasoningPhase N) (d nb : N.α) :
    (recordPhase s p d nb).patterns_discovered =
      s.patterns_discovered + p.pattern_captures.length :=
  match p.level with
  | ThoughtLevel.local => rfl
  | ThoughtLevel.global => rfl
  | ThoughtLevel.meta => rfl

theorem record_average_formula {N : NumSem} (s : OrchestratorStatistics N) (p : ReasoningPhase N) (d nb : N.α) :
    (recordPhase s p d nb).average_convergence_time =
      N.add s.average_convergence_time
        (N.div (N.sub d s.average_convergence_time) (N.ofNat (s.total_phases + 1))) :=
  match p.level with
  | ThoughtLevel.local => rfl
  | ThoughtLevel.global => rfl
  | ThoughtLevel.meta => rfl

end OrchestratorStatistics

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

def perturbNode {N : NumSem} (n : Node N) (sample : N.α) : Node N :=
  let p := Prng.perturbValue sample
  { n with phase := N.add n.phase p, qubit := Qubit.perturb n.qubit p }
def perturbNodesAux {N : NumSem} :
    Nat → List (Node N) → Optimizer N → List (Node N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, n :: ns, o =>
      let r := Optimizer.random o
      let rest := perturbNodesAux k ns r.fst
      (perturbNode n r.snd :: rest.fst, rest.snd)
def perturbLocalNodes {N : NumSem} (o : Orch N) : Orch N :=
  let r := perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt
  { o with graph := { o.graph with nodes := r.fst }, opt := r.snd }
def updateEdge {N : NumSem} (e : Edge N) (sample : N.α) : Edge N :=
  Edge.localPerturb e (Prng.edgeDelta sample)
def updateEntry {N : NumSem} (ee : EdgeEntry N) (opt : Optimizer N) : EdgeEntry N × Optimizer N :=
  let mapped := ee.items.map (fun e => updateEdge e N.half)
  ({ ee with items := mapped }, opt)
def updateEntriesAux {N : NumSem} :
    Nat → List (EdgeEntry N) → Optimizer N → List (EdgeEntry N) × Optimizer N
  | 0, xs, o => (xs, o)
  | Nat.succ k, [], o => ([], o)
  | Nat.succ k, ee :: es, o =>
      let a := updateEntry ee o
      let b := updateEntriesAux k es a.snd
      (a.fst :: b.fst, b.snd)
def updateLocalEdges {N : NumSem} (o : Orch N) : Orch N :=
  let r := updateEntriesAux o.update_edge_limit o.graph.edges o.opt
  { o with graph := { o.graph with edges := r.fst }, opt := r.snd }

theorem perturb_limit_def {N : NumSem} (o : Orch N) :
    (perturbLocalNodes o).graph.nodes = (perturbNodesAux o.perturb_node_limit o.graph.nodes o.opt).fst := rfl

theorem update_limit_def {N : NumSem} (o : Orch N) :
    (updateLocalEdges o).graph.edges = (updateEntriesAux o.update_edge_limit o.graph.edges o.opt).fst := rfl

theorem selected_phase_formula {N : NumSem} (n : Node N) (s : N.α) :
    (perturbNode n s).phase = N.add n.phase (Prng.perturbValue s) := rfl

theorem processed_weight_clamped {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).weight =
      N.clamp (N.add e.weight (Prng.edgeDelta s)) N.zero N.one := rfl

theorem processed_corr_exact {N : NumSem} (e : Edge N) (s : N.α) :
    (updateEdge e s).quantum_correlation.re =
      N.add e.quantum_correlation.re (N.mul (Prng.edgeDelta s) N.tenth) := rfl

end LocalMutation

namespace GlobalMutation

def transformNode {N : NumSem} (t : SymmetryTransform N) (n : Node N) : Node N :=
  let q : QuantumState N :=
    { amplitude_real := n.qubit.a.re,
      amplitude_imag := n.qubit.a.im,
      phase := n.phase,
      entanglement_degree := N.zero }
  let z := t.act q
  { n with qubit := { a := { re := z.amplitude_real, im := z.amplitude_imag } }, phase := z.phase }
def transformFirst {N : NumSem} :
    Nat → SymmetryTransform N → List (Node N) → List (Node N)
  | 0, t, xs => xs
  | Nat.succ k, t, [] => []
  | Nat.succ k, t, n :: ns => transformNode t n :: transformFirst k t ns
def applyTransforms {N : NumSem} :
    Nat → List (SymmetryTransform N) → List (Node N) → List (Node N)
  | limit, [], ns => ns
  | limit, t :: ts, ns => applyTransforms limit ts (transformFirst limit t ns)

inductive TransformRel {N : NumSem} :
    Orch N → RunResult OrchestratorError (Orch N) Unit → Prop where
  | ok (o : Orch N) (ts : List (SymmetryTransform N)) :
      Optimizer.DetectRel o.opt o.graph (RunResult.ok o.opt ts) →
      TransformRel o
        (RunResult.ok { o with graph := { o.graph with nodes := applyTransforms o.transform_node_limit ts o.graph.nodes } } ())
  | fail (o : Orch N) :
      Optimizer.DetectRel o.opt o.graph
        (RunResult.err o.opt OrchestratorError.symmetryDetectionFailure) →
      TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure)

def totalDim {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add e.fractal_dimension (totalDim es)
def rebalanceAll {N : NumSem} (g : Graph N) (avg : N.α) : Graph N :=
  { g with edges := g.edges.map (fun ee => { ee with items := ee.items.map (fun e => Edge.rebalance e avg) }) }

inductive RebalanceRel {N : NumSem} (g : Graph N) : Graph N → Prop where
  | empty : Graph.edgeCount g = 0 → RebalanceRel g g
  | nonempty : ∀ c, Graph.edgeCount g = c + 1 →
      RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1))))

theorem detection_error {N : NumSem} (o : Orch N) (h : o.opt.detection_ok = false) :
    TransformRel o (RunResult.err o OrchestratorError.symmetryDetectionFailure) :=
  TransformRel.fail o (Optimizer.detect_error h)

theorem rebalance_empty {N : NumSem} (g : Graph N) (h : Graph.edgeCount g = 0) :
    RebalanceRel g g := RebalanceRel.empty h

theorem rebalance_nonempty {N : NumSem} (g : Graph N) (c : Nat) (h : Graph.edgeCount g = c + 1) :
    RebalanceRel g (rebalanceAll g (N.div (totalDim (Energy.flattenEdges g)) (N.ofNat (c + 1)))) :=
  RebalanceRel.nonempty c h

end GlobalMutation

structure ReasoningOrchestrator (N : NumSem) where
  graph : Graph N
  opt : Optimizer N
  kernel : ChaosKernel
  phase_history : List (ReasoningPhase N)
  statistics : OrchestratorStatistics N
  fast_inner_steps : Nat
  slow_outer_steps : Nat
  hierarchical_depth : Nat
  perturb_node_limit : Nat
  update_edge_limit : Nat
  transform_node_limit : Nat
  next_phase_id : Nat
  max_phase_id : Nat
  store : Store
deriving Repr

namespace ReasoningOrchestrator

def historyValid {N : NumSem} (xs : List (ReasoningPhase N)) : Prop :=
  ∀ p, p ∈ xs → ReasoningPhase.valid p
def valid {N : NumSem} (o : ReasoningOrchestrator N) : Prop :=
  Graph.valid o.graph ∧ Optimizer.valid o.opt ∧ ChaosKernel.valid o.kernel ∧
  historyValid o.phase_history ∧ OrchestratorStatistics.valid o.statistics ∧ Store.valid o.store
def init {N : NumSem} (g : Graph N) (opt : Optimizer N) (k : ChaosKernel)
    (st : Store) (time : Int) : ReasoningOrchestrator N :=
  { graph := g,
    opt := opt,
    kernel := k,
    phase_history := [],
    statistics := OrchestratorStatistics.init time,
    fast_inner_steps := 50,
    slow_outer_steps := 10,
    hierarchical_depth := 3,
    perturb_node_limit := 10,
    update_edge_limit := 10,
    transform_node_limit := 5,
    next_phase_id := 1,
    max_phase_id := 18446744073709551615,
    store := st }
def deinit {N : NumSem} (o : ReasoningOrchestrator N) : ReasoningOrchestrator N :=
  { o with store := { o.store with state := StoreState.freed },
           phase_history := o.phase_history.map ReasoningPhase.deinit }
def setParameters {N : NumSem} (o : ReasoningOrchestrator N) (inner outer depth : Nat) : ReasoningOrchestrator N :=
  { o with fast_inner_steps := inner, slow_outer_steps := outer, hierarchical_depth := depth }
def setProcessingLimits {N : NumSem} (o : ReasoningOrchestrator N) (pn ue tn : Nat) : ReasoningOrchestrator N :=
  { o with perturb_node_limit := pn, update_edge_limit := ue, transform_node_limit := tn }

inductive AllocPhaseIdRel {N : NumSem} :
    ReasoningOrchestrator N → RunResult OrchestratorError (ReasoningOrchestrator N) Nat → Prop where
  | ok (o : ReasoningOrchestrator N) :
      o.next_phase_id < o.max_phase_id →
      AllocPhaseIdRel o
        (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id)
  | overflow (o : ReasoningOrchestrator N) :
      o.max_phase_id ≤ o.next_phase_id →
      AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow)

theorem init_fast {N : NumSem} (g : Graph N) (op : Optimizer N) (k : ChaosKernel) (st : Store) (tm : Int) :
    (init g op k st tm).fast_inner_steps = 50 := rfl

theorem init_valid {N : NumSem} {g : Graph N} {op : Optimizer N} {k : ChaosKernel} {st : Store} {tm : Int}
    (hg : Graph.valid g) (ho : Optimizer.valid op) (hk : ChaosKernel.valid k) :
    valid (init g op k st tm) :=
  And.intro hg
    (And.intro ho
      (And.intro hk
        (And.intro (fun p h => False.elim h)
          (And.intro (OrchestratorStatistics.init_valid tm) True.intro))))

theorem deinit_store_freed {N : NumSem} (o : ReasoningOrchestrator N) :
    (deinit o).store.state = StoreState.freed := rfl

theorem setParameters_fast {N : NumSem} (o : ReasoningOrchestrator N) (i u d : Nat) :
    (setParameters o i u d).fast_inner_steps = i := rfl

theorem setProcessingLimits_perturb {N : NumSem} (o : ReasoningOrchestrator N) (p e t : Nat) :
    (setProcessingLimits o p e t).perturb_node_limit = p := rfl

theorem alloc_id_ok {N : NumSem} (o : ReasoningOrchestrator N) (h : o.next_phase_id < o.max_phase_id) :
    AllocPhaseIdRel o (RunResult.ok { o with next_phase_id := o.next_phase_id + 1 } o.next_phase_id) :=
  AllocPhaseIdRel.ok o h

theorem alloc_id_overflow {N : NumSem} (o : ReasoningOrchestrator N) (h : o.max_phase_id ≤ o.next_phase_id) :
    AllocPhaseIdRel o (RunResult.err o OrchestratorError.phaseIdOverflow) :=
  AllocPhaseIdRel.overflow o h

end ReasoningOrchestrator

namespace Energy

def edgeContribution {N : NumSem} (e : Edge N) : N.α :=
  N.add (N.mul e.weight e.fractal_dimension) (Cx.mag e.quantum_correlation)
def sumEdges {N : NumSem} : List (Edge N) → N.α
  | [] => N.zero
  | e :: es => N.add (edgeContribution e) (sumEdges es)
def flattenEdges {N : NumSem} (g : Graph N) : List (Edge N) :=
  (g.edges.map (fun ee => ee.items)).foldl List.append []
def sumNodes {N : NumSem} : List (Node N) → N.α
  | [] => N.zero
  | n :: ns => N.add (N.cos n.phase) (sumNodes ns)
def total {N : NumSem} (g : Graph N) : N.α :=
  N.add (sumEdges (flattenEdges g)) (sumNodes g.nodes)

inductive ComputeRel {N : NumSem} (g : Graph N) : N.α → Prop where
  | empty : Graph.contributionCount g = 0 → ComputeRel g N.oneMillion
  | nonempty : ∀ c, Graph.contributionCount g = c + 1 →
      ComputeRel g (N.div (total g) (N.ofNat (c + 1)))

theorem empty_energy {N : NumSem} (g : Graph N) (h : Graph.contributionCount g = 0) :
    ComputeRel g N.oneMillion := ComputeRel.empty h

theorem nonempty_energy {N : NumSem} (g : Graph N) (c : Nat)
    (h : Graph.contributionCount g = c + 1) :
    ComputeRel g (N.div (total g) (N.ofNat (c + 1))) := ComputeRel.nonempty c h

theorem count_equals {N : NumSem} (g : Graph N) :
    Graph.contributionCount g = Graph.nodeCount g + Graph.edgeCount g := rfl

end Energy

namespace LocalMutation

