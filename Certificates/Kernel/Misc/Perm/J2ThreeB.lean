module

public import Certificates.Kernel.Misc.Perm.J2C3A
public import Certificates.Data.J2ThreeB
public import Certificates.Data.Kernel.J2ThreeBK
public import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2ThreeB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.J2ThreeBK
open CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.J2Cover
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.C89090
open CFSG.RankThree.PartTwo.J2Residue CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CertificateChecks.KernelMisc.J2C3 (AB Z I hab hz hI p3)

theorem kA : checkAK (AB 0) (AB 1) I = true := by decide +kernel

theorem kB : checkBK (AB 0) (AB 1) I Z CertificateChecks.KernelMisc.J2C3.P3P.F = true := by
  decide +kernel

abbrev CK (p : Nat) : Prop := canonK 315 9 (mask 9) (315 * 9) p = true

theorem cA : CK (AB 0) := by quickRfl
theorem cB : CK (AB 1) := by quickRfl
theorem cI : CK I := by quickRfl
theorem cZ : CK Z := by quickRfl

theorem cP : ∀ j < 27, CK (CertificateChecks.KernelMisc.J2C3.P3P.F j) := by
  have h : (List.range 27).all (fun j => canonK 315 9 (mask 9) (315 * 9)
      (CertificateChecks.KernelMisc.J2C3.P3P.F j)) = true := by quickRfl
  intro j hj
  exact List.all_eq_true.1 h j (List.mem_range.2 hj)

theorem pc_canon {p q : Nat} (hp : CK p) (hq : CK q) : CK (pc p q) := canonK_pcomp hp hq

theorem comp_eq {p q : Nat} (hp : CK p) (hq : CK q) :
    compA 315 (unpack 315 9 p) (unpack 315 9 q) = unpack 315 9 (pc p q) := compA_unpack hp hq

theorem eq_eq {p q : Nat} (hp : CK p) (hq : CK q) :
    eqA 315 (unpack 315 9 p) (unpack 315 9 q) = Nat.beq p q := eqA_unpack hp hq

theorem strictB_app' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictL_app (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

theorem forceL_app : ∀ (L : List Nat) (k : List Nat → Bool), forceL L k = k L
  | [], _ => rfl
  | x :: xs, k => by
    change strictB x (fun x' => forceL xs fun r => k (x' :: r)) = k (x :: xs)
    rw [strictB_app', forceL_app xs]

theorem any_map_congr {α β : Type} (L : List α) (m : α → β) (f : β → Bool) (g : α → Bool)
    (h : ∀ a ∈ L, f (m a) = g a) : (L.map m).any f = L.any g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, List.any_cons]
    rw [h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem all_map_congr {α β : Type} (L : List α) (m : α → β) (f : β → Bool) (g : α → Bool)
    (h : ∀ a ∈ L, f (m a) = g a) : (L.map m).all f = L.all g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, List.all_cons]
    rw [h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem all_congr' {α : Type} (L : List α) (f g : α → Bool) (h : ∀ a ∈ L, f a = g a) :
    L.all f = L.all g := by
  simpa using all_map_congr L id f g h

theorem gen_eq (k : Nat) :
    C280.genA k = unpack 315 9 (gen (AB 0) (AB 1) k) ∧ CK (gen (AB 0) (AB 1) k) := by
  by_cases h : k = 0
  · subst h
    exact ⟨by rw [C280.genA, if_pos rfl]; exact hab 0 (by norm_num), cA⟩
  · have hb : Nat.beq k 0 = false := by
      cases e : Nat.beq k 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    have e : gen (AB 0) (AB 1) k = AB 1 := by
      unfold gen
      rw [hb]
    rw [e, C280.genA, if_neg h]
    exact ⟨hab 1 (by norm_num), cB⟩

theorem wd_eq : ∀ w : List Nat,
    C280.wordA w = unpack 315 9 (wd (AB 0) (AB 1) w) ∧ CK (wd (AB 0) (AB 1) w)
  | [] => ⟨hI.symm, cI⟩
  | k :: w => by
    obtain ⟨ih1, ih2⟩ := wd_eq w
    obtain ⟨g1, g2⟩ := gen_eq k
    have e : wd (AB 0) (AB 1) (k :: w) = pc (gen (AB 0) (AB 1) k) (wd (AB 0) (AB 1) w) := by
      change strictN (wordTabK 315 9 (mask 9) (pidn 315 9) (gen (AB 0) (AB 1)) w)
        (fun acc => pcomp 315 9 (mask 9) (gen (AB 0) (AB 1) k) acc) = _
      rw [strictN_app']
      rfl
    have e2 : C280.wordA (k :: w) = compA 315 (C280.genA k) (C280.wordA w) := rfl
    rw [e, e2, ih1, g1]
    exact ⟨comp_eq g2 ih2, pc_canon g2 ih2⟩

@[expose] noncomputable def Y : Nat := wd (AB 0) (AB 1) y0W

theorem hY : y0A () = unpack 315 9 Y := (wd_eq y0W).1

theorem cY : CK Y := (wd_eq y0W).2

theorem prods_eq : ∀ ps : List (List Nat × List Nat),
    (ps.flatMap fun p =>
      let a := C280.wordA p.1
      let b := C280.wordA p.2
      [compA 315 a b, compA 315 (compA 315 a (unpack 315 9 Y)) b,
        compA 315 (compA 315 a (compA 315 (unpack 315 9 Y) (unpack 315 9 Y))) b]) =
      (prodsOf (AB 0) (AB 1) Y ps).map (unpack 315 9) ∧
    ∀ t ∈ prodsOf (AB 0) (AB 1) Y ps, CK t
  | [] => ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | p :: ps => by
    obtain ⟨ih1, ih2⟩ := prods_eq ps
    obtain ⟨a1, a2⟩ := wd_eq p.1
    obtain ⟨b1, b2⟩ := wd_eq p.2
    have e : prodsOf (AB 0) (AB 1) Y (p :: ps) =
        [pc (wd (AB 0) (AB 1) p.1) (wd (AB 0) (AB 1) p.2),
          pc (pc (wd (AB 0) (AB 1) p.1) Y) (wd (AB 0) (AB 1) p.2),
          pc (pc (wd (AB 0) (AB 1) p.1) (pc Y Y)) (wd (AB 0) (AB 1) p.2)] ++
        prodsOf (AB 0) (AB 1) Y ps := by
      unfold prodsOf
      rw [List.flatMap_cons, strictL_app, strictL_app]
    rw [e, List.flatMap_cons, ih1, List.map_append]
    refine ⟨?_, ?_⟩
    · simp only [a1, b1, List.map_cons, List.map_nil]
      rw [comp_eq a2 b2, comp_eq a2 cY, comp_eq (pc_canon a2 cY) b2, comp_eq cY cY,
        comp_eq a2 (pc_canon cY cY), comp_eq (pc_canon a2 (pc_canon cY cY)) b2]
    · intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        · exact pc_canon a2 b2
        · exact pc_canon (pc_canon a2 cY) b2
        · exact pc_canon (pc_canon a2 (pc_canon cY cY)) b2
      · exact ih2 t ht

theorem hProds : prods89090 () = (prodsOf (AB 0) (AB 1) Y pairW).map (unpack 315 9) := by
  unfold prods89090
  rw [hY]
  exact (prods_eq pairW).1

theorem parity_eq {J : Nat} (hJ : CK J) {T : List Nat} (hT : ∀ t ∈ T, CK t) :
    ((T.map (unpack 315 9)).any (fun t => eqA 315 t (unpack 315 9 J)) &&
      (T.map (unpack 315 9)).all fun t =>
        ((T.map (unpack 315 9)).countP fun u => eqA 315 u t) % 2 ==
          if eqA 315 t (unpack 315 9 J) then 1 else 0) = parityK J T := by
  unfold parityK
  have hc : ∀ t ∈ T, ((T.map (unpack 315 9)).countP fun u => eqA 315 u (unpack 315 9 t)) =
      T.countP fun u => Nat.beq u t := by
    intro t ht
    rw [List.countP_map]
    exact List.countP_congr fun u hu => by
      simp only [Function.comp_apply, eq_eq (hT u hu) (hT t ht)]
  rw [any_map_congr T (unpack 315 9) (fun t => eqA 315 t (unpack 315 9 J))
      (fun t => Nat.beq t J) fun t ht => eq_eq (hT t ht) hJ,
    all_map_congr T (unpack 315 9)
      (fun t => ((T.map (unpack 315 9)).countP fun u => eqA 315 u t) % 2 ==
        if eqA 315 t (unpack 315 9 J) then 1 else 0)
      (fun t => (T.countP fun u => Nat.beq u t) % 2 == if Nat.beq t J then 1 else 0)
      fun t ht => by
        try simp only []
        rw [hc t ht, eq_eq (hT t ht) hJ]]

theorem checkA_eq {J y : Nat} (hJ : CK J) (hy : CK y) {T : List Nat} (hT : ∀ t ∈ T, CK t) :
    (eqA 315 (compA 315 (unpack 315 9 y) (compA 315 (unpack 315 9 y) (unpack 315 9 y)))
      (unpack 315 9 J) && ((T.map (unpack 315 9)).any (fun t => eqA 315 t (unpack 315 9 J)) &&
        (T.map (unpack 315 9)).all fun t =>
          ((T.map (unpack 315 9)).countP fun u => eqA 315 u t) % 2 ==
            if eqA 315 t (unpack 315 9 J) then 1 else 0)) =
      (Nat.beq (pc y (pc y y)) J && parityK J T) := by
  rw [comp_eq hy hy, comp_eq hy (pc_canon hy hy), eq_eq (pc_canon hy (pc_canon hy hy)) hJ,
    parity_eq hJ hT]

theorem chkA : check89090A () = true := by
  have hk := kA
  unfold checkAK at hk
  rw [strictB_app', strictB_app', strictB_app', strictB_app', forceL_app] at hk
  have e : check89090A () = (eqA 315 (compA 315 (y0A ()) (compA 315 (y0A ()) (y0A ())))
      (idA 315) && ((prods89090 ()).any (fun t => eqA 315 t (idA 315)) &&
        (prods89090 ()).all fun t =>
          ((prods89090 ()).countP fun u => eqA 315 u t) % 2 ==
            if eqA 315 t (idA 315) then 1 else 0)) := by
    unfold check89090A
    simp only [Bool.and_assoc]
  rw [e, hProds, hY, ← hI, checkA_eq cI cY (prods_eq pairW).2]
  exact hk

theorem pt_eq {J Zp y p : Nat} {C : List Nat} (hJ : CK J) (hZ : CK Zp) (hy : CK y) (hp : CK p)
    (hC : ∀ c ∈ C, CK c) :
    ((eqA 315 (unpack 315 9 p) (unpack 315 9 J) || eqA 315 (unpack 315 9 p) (unpack 315 9 Zp) ||
        eqA 315 (unpack 315 9 p) (compA 315 (unpack 315 9 Zp) (unpack 315 9 Zp))) ||
      (C.map (unpack 315 9)).any fun c =>
        eqA 315 (compA 315 c (unpack 315 9 y)) (compA 315 (unpack 315 9 p) c)) =
      ptK J Zp y C p := by
  unfold ptK
  rw [comp_eq hZ hZ, eq_eq hp hJ, eq_eq hp hZ, eq_eq hp (pc_canon hZ hZ)]
  congr 1
  refine any_map_congr C (unpack 315 9)
    (fun c => eqA 315 (compA 315 c (unpack 315 9 y)) (compA 315 (unpack 315 9 p) c))
    (fun c => Nat.beq (pc c y) (pc p c)) fun c hc => ?_
  try simp only []
  rw [comp_eq (hC c hc) hy, comp_eq hp (hC c hc),
    eq_eq (pc_canon (hC c hc) hy) (pc_canon hp (hC c hc))]

theorem chkB : check89090B () = true := by
  have hk := kB
  unfold checkBK at hk
  rw [strictB_app', strictB_app', strictB_app', strictB_app', strictB_app', forceL_app] at hk
  have hC : ∀ c ∈ conjW.map (wd (AB 0) (AB 1)), CK c := by
    intro c hc
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hc
    exact (wd_eq w).2
  have hCe : conjW.map C280.wordA = (conjW.map (wd (AB 0) (AB 1))).map (unpack 315 9) := by
    rw [List.map_map]
    exact List.map_congr_left fun w _ => (wd_eq w).1
  unfold check89090B
  simp only []
  rw [hY, hCe]
  refine Eq.trans (all_congr' (List.range 27)
    (fun j => inZ cP3.pts[j]! || ((conjW.map (wd (AB 0) (AB 1))).map (unpack 315 9)).any fun c =>
      eqA 315 (compA 315 c (unpack 315 9 Y)) (compA 315 cP3.pts[j]! c))
    (fun j => strictB (CertificateChecks.KernelMisc.J2C3.P3P.F j) fun p =>
      ptK I Z Y (conjW.map (wd (AB 0) (AB 1))) p) fun j hj => ?_) hk
  try simp only []
  have hj' := List.mem_range.1 hj
  rw [strictB_app', p3.2.1 j hj']
  unfold inZ
  rw [← hI, hz]
  exact pt_eq cI cZ cY (cP j hj') hC

open Certificates in
theorem facts : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.C89090.check89090A () = true ∧
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.C89090.check89090B () = true := ⟨chkA, chkB⟩

end CertificateChecks.KernelMisc.J2ThreeB

end
