module

public import Certificates.Kernel.LocalQT.TabA2.F4043
public import Certificates.Kernel.LocalQT.TabA2.C4045
public import Certificates.Kernel.LocalQT.TabA2.C4045R0
public import Certificates.Kernel.LocalQT.TabA2.C4045R1
public import Certificates.Kernel.LocalQT.TabA2.C4045R2
public import Certificates.Kernel.LocalQT.TabA2.C4045R3
public import Certificates.Kernel.LocalQT.TabA2.C4045R4
public import Certificates.Kernel.LocalQT.TabA2.C4045R5
public import Certificates.Kernel.LocalQT.TabA2.C4045R6
public import Certificates.Kernel.LocalQT.TabA2.C4045R7
public import Certificates.Kernel.LocalQT.TabA2.C4045R8
public import Certificates.Kernel.LocalQT.TabA2.C4045R9
public import Certificates.Kernel.LocalQT.TabA2.C4045R10
public import Certificates.Kernel.LocalQT.TabA2.C4045R11
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL34CheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.LQT.TL.R CFSG.KD.LQT.TL.ckR 3780
#kqb_all CFSG.KD.LQT.TL.T CFSG.KD.LQT.TL.ckT 315

namespace CFSG.KD.LQT.TL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.TabA2 CFSG.KS.TabL34
open CFSG.PSL3Four.Native CFSG.KD.LQT.TA CFSG.QuasithinUnique.Id2519.Tab.L34

theorem gensR : GensOK 42 6 6 R.G gTabs := gensOK_of (by quickRfl)

theorem rcnt_eq : R.cnt = 241920 := Nat.eq_of_beq_eq_true cnt_ok

theorem rs_spec {G T PL POS SRT SRI ST CG : Nat → Nat} {R0 kC cnt lo len : Nat}
    (h : rsK G T PL POS SRT SRI ST CG R0 kC cnt lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt →
      penumPtK 42 6 (mask 6) (42 * 6) false G G 6 cnt T PL POS SRT SRI i = true ∧
        centK ST CG R0 kC (T i) = true := by
  intro i h1 h2 h3
  have h' := allN_spec h (i - lo) (by omega)
  rw [strictB_app'] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i cnt = true := Eq.mpr Nat.blt_eq h3
  rw [hb] at h'
  exact (bAnd_iff _ _).1 h'

theorem rpts : ∀ i < R.cnt,
    penumPtK 42 6 (mask 6) (42 * 6) false R.G R.G 6 R.cnt R.T R.PL R.POS R.SRT R.SRI i = true ∧
      centK S.T CG (X 2) kC (R.T i) = true := by
  intro i hi
  rw [rcnt_eq] at hi
  refine chunks (N := 3780) (L := 64) (Q := fun i =>
    penumPtK 42 6 (mask 6) (42 * 6) false R.G R.G 6 R.cnt R.T R.PL R.POS R.SRT R.SRI i = true ∧
      centK S.T CG (X 2) kC (R.T i) = true) (by norm_num) (fun s hs j h1 h2 => ?_) i hi
  have h2' : j < s * 64 + 64 := h2
  exact rs_spec (R.all s hs) j h1 h2 (by rw [rcnt_eq]; omega)

theorem ts_spec {ST TW : Nat → Nat} {R0 cnt lo len : Nat} (h : tsK ST TW R0 cnt lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt → twK ST TW R0 cnt i = true := by
  intro i h1 h2 h3
  have h' := allN_spec h (i - lo) (by omega)
  rw [strictB_app'] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i cnt = true := Eq.mpr Nat.blt_eq h3
  rw [hb] at h'
  exact h'

theorem tpts : ∀ i < S.cnt, twK S.T TW (X 2) S.cnt i = true := by
  intro i hi
  rw [cnt_eq] at hi
  refine chunks (N := 315) (L := 64) (Q := fun i => twK S.T TW (X 2) S.cnt i = true)
    (by norm_num) (fun s hs j h1 h2 => ?_) i hi
  have h2' : j < s * 64 + 64 := h2
  exact ts_spec (T.all s hs) j h1 h2 (by rw [cnt_eq]; omega)

@[expose] noncomputable def ER : Enum := penumRec 42 6 R.cnt R.T R.PL

theorem hER : enumBFS 42 gTabs 241920 = ER :=
  (penumK_left_sound hn gensR hd_ok fun i hi => (rpts i hi).1).1

theorem penumRec_size (n w cnt : Nat) (T PL : Nat → Nat) :
    (penumRec n w cnt T PL).tabs.size = cnt := by
  simp [penumRec]

theorem penumRec_get {n w cnt k : Nat} {T PL : Nat → Nat} (hk : k < cnt) :
    (penumRec n w cnt T PL).tabs[k]! = unpack n w (T k) := by
  rw [getElem!_pos _ k (by rw [penumRec_size]; exact hk)]
  simp [penumRec]

theorem rtabs_size : ER.tabs.size = R.cnt := penumRec_size _ _ _ _ _

theorem pTR {k : Nat} (hk : k < R.cnt) : P ER.tabs[k]! (R.T k) :=
  ⟨penumRec_get hk, penumPt_canon (rpts k hk).1⟩

theorem allBelow_false {A : Array Tab} {f : Tab → Bool} {x : Tab} (hx : x ∈ A.toList)
    (h : f x = false) : allBelow A.size (fun i => f A[i]!) = false := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hx
  have hi' : i < A.size := by simpa using hi
  unfold allBelow
  rw [Bool.eq_false_iff, ne_eq, List.all_eq_true]
  intro hall
  have := hall i (List.mem_range.2 hi')
  rw [getElem!_pos A i hi'] at this
  simp only [Array.getElem_toList] at e
  rw [e, h] at this
  exact absurd this (by decide)

theorem cg_facts {c : Nat} (hc : c < kC) : CG c < S.cnt ∧
    pc (S.T (CG c)) (X 2) = pc (X 2) (S.T (CG c)) := by
  have h := allN_spec cg_ok c hc
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Eq.mp Nat.blt_eq h1, Nat.eq_of_beq_eq_true h2⟩

theorem cent2Scan_true : cent2Scan = true := by
  unfold cent2Scan
  dsimp only
  rw [hE, hER]
  refine allBelow_of fun k hk => ?_
  rw [rtabs_size] at hk
  have hX := pTR hk
  have h := (rpts k hk).2
  rw [beqP hX idP, beqP hX pR]
  unfold centK at h
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  by_cases h1 : Nat.beq (R.T k) idn = true
  · left
    right
    exact h1
  by_cases h2 : Nat.beq (R.T k) (X 2) = true
  · right
    exact h2
  · left
    left
    rw [Bool.eq_false_of_ne_true h1, Bool.eq_false_of_ne_true h2] at h
    · obtain ⟨c, hc, e⟩ := anyK_spec h
      obtain ⟨c, hc, e⟩ := anyK_spec h
      rw [strictB_app'] at e
      obtain ⟨hcn, hcc⟩ := cg_facts hc
      have hY := pT hcn
      have hm : E.tabs[CG c]! ∈ (centTabs 42 E.tabs r₂T).toList := by
        rw [memC, commP hY, hcc, Nat.beq_refl]
        exact ⟨memE_of hcn, rfl⟩
      refine allBelow_false (f := fun y => comp 42 ER.tabs[k]! y == comp 42 y ER.tabs[k]!)
        hm ?_
      rw [beqP (compP hX hY) (compP hY hX)]
      cases hb : Nat.beq (pc (R.T k) (S.T (CG c))) (pc (S.T (CG c)) (R.T k))
      · rfl
      · rw [hb] at e
        exact absurd e (by decide)

theorem tw_facts {k : Nat} (hk : k < S.cnt) (hc : pc (S.T k) (X 2) = pc (X 2) (S.T k))
    (hs : pc (S.T k) (S.T k) = idn) (hne : S.T k ≠ idn) : TW k < S.cnt ∧
      invOK (S.T (TW k)) (pinv (S.T (TW k))) = true ∧
      pc (pc (pinv (S.T (TW k))) (X 2)) (S.T (TW k)) = pc (X 2) (S.T k) := by
  have h := tpts k hk
  have hb : Nat.beq (S.T k) idn = false := by
    cases hb : Nat.beq (S.T k) idn
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hne
  unfold twK at h
  rw [strictB_app', hc, hs, Nat.beq_refl, Nat.beq_refl, hb] at h
  change strictB (TW k) _ = true at h
  rw [strictB_app'] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [strictB_app', strictB_app'] at h2
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  exact ⟨Eq.mp Nat.blt_eq h1, h2, Nat.eq_of_beq_eq_true h3⟩

theorem twistScan_true : twistScan = true := by
  unfold twistScan
  dsimp only
  rw [hE]
  refine allBelow_mem (f := fun x => x == idTab 42 || !(comp 42 x x == idTab 42) ||
    anyBelow E.tabs.size fun k =>
      (invTab 42 E.tabs[k]!).size == 42 && comp 42 (invTab 42 E.tabs[k]!) E.tabs[k]! == idTab 42 &&
        comp 42 (comp 42 (invTab 42 E.tabs[k]!) r₂T) E.tabs[k]! == comp 42 r₂T x) fun x hx => ?_
  obtain ⟨hxE, hxc⟩ := memC.1 hx
  obtain ⟨k, hk, hX⟩ := memE hxE
  rw [commP hX] at hxc
  have hc := Nat.eq_of_beq_eq_true hxc
  simp only [Bool.or_eq_true, Bool.not_eq_true', beqP hX idP, beqP (compP hX hX) idP]
  by_cases hne : S.T k = idn
  · left
    left
    rw [hne, Nat.beq_refl]
  by_cases hs : pc (S.T k) (S.T k) = idn
  · right
    obtain ⟨hy, hinv, he⟩ := tw_facts hk hc hs hne
    have hY := pT hy
    obtain ⟨hYI, h1, h2⟩ := invP hY hinv
    refine anyBelow_of (i := TW k) (by rw [tabs_size]; exact hy) ?_
    simp only [Bool.and_eq_true]
    refine ⟨⟨h1, h2⟩, ?_⟩
    rw [beqP (compP (compP hYI pR) hY) (compP pR hX), he, Nat.beq_refl]
  · left
    right
    cases hb : Nat.beq (pc (S.T k) (S.T k)) idn
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hs

end CFSG.KD.LQT.TL

end
