module

public import Certificates.Kernel.Sporadic.OddCore.J2CnF
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineJTwoCertData

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.J2EA

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.MulH CFSG.SeitzReduction.SporadicRefine
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn

@[expose] noncomputable def T (i : Nat) : Nat := J2SY.T i

@[expose] noncomputable def invoK (x : Nat) : Bool := Nat.beq (pc x x) idK

@[expose] noncomputable def movK (x : Nat) : Nat :=
  (List.range 315).countP fun i => pg 9 (mask 9) x i != i

@[expose] noncomputable def closedK (I : List Nat) : Bool :=
  I.all fun y => I.all fun z => I.any fun t => Nat.beq (pc (T y) (T z)) (T t)

@[expose] noncomputable def countAt (I₁ I₂ : List Nat) (i : Nat) : Bool :=
  I₁.contains i || I₂.contains i || !sK (T i) || !invoK (T i) ||
    decide (((List.range 256).filter fun y => sK (T y) && invoK (T y) && commK (T y) (T i)).length
      < 16)

@[expose] noncomputable def normK (m : Nat) (I : List Nat) : Bool :=
  I.all fun y => I.any fun t => Nat.beq (pc (T m) (T y)) (pc (T t) (T m))

@[expose] noncomputable def twoK (m : Nat) (I : List Nat) : Bool :=
  I.any fun a => I.any fun b => commK (T a) (T m) && commK (T b) (T m) && !Nat.beq (T a) idK &&
    !Nat.beq (T b) idK && movK (T a) != movK (T b)

@[expose] noncomputable def suppAt (I₁ I₂ : List Nat) (m : Nat) : Bool :=
  sK (T m) || !involK (T m) || [I₁, I₂].all fun I => !normK m I || twoK m I

theorem enum_eq : j2SylEnum = (hRec 315 9 J2SY.cnt J2SY.T J2SY.PL).1 := by
  unfold j2SylEnum
  rw [sy_eq, recSY.1]

theorem cnt : J2SY.cnt = 256 := sizes.2.2.2.1

theorem size_eq : j2SylEnum.size = 256 := by
  rw [enum_eq, hRec_size, cnt]

theorem canonT {i : Nat} (hi : i < 256) : canonK 315 9 (mask 9) (315 * 9) (T i) = true :=
  canonR (pe_all' syE) i (by rw [cnt]; exact hi)

theorem get_eq {i : Nat} (hi : i < 256) : j2SylEnum[i]! = tabT (unpack 315 9 (T i)) := by
  rw [enum_eq, hRec_get (by rw [cnt]; exact hi)]
  rfl

theorem invoOK_eq {x : Nat} (hx : canonK 315 9 (mask 9) (315 * 9) x = true) :
    invoOK 315 (tabT (unpack 315 9 x)) = invoK x := by
  rw [invoOK_eq' (by norm_num), compT_unpack hx hx, hid, tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp hx hx) hidc]
  rfl

theorem idEq {x : Nat} (hx : canonK 315 9 (mask 9) (315 * 9) x = true) :
    tblEq 315 (tabT (unpack 315 9 x)) (idT 315) = Nat.beq x idK := by
  rw [hid, tblEq_unpack hx hidc]
  rfl

theorem moved_eq {x : Nat} (hx : canonK 315 9 (mask 9) (315 * 9) x = true) :
    movedCount 315 (tabT (unpack 315 9 x)) = movK x := by
  unfold movedCount movK
  refine List.countP_congr fun i hi => ?_
  rw [List.mem_range] at hi
  rw [ap_tabT _ (unpack_lt hx), CFSG.KS.Raw.unpack, getElem!_pos _ i (by simpa using hi),
    Array.getElem_ofFn]

theorem all_congr' {l : List Nat} {p q : Nat → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q :=
  Bool.eq_iff_iff.2 (by
    rw [List.all_eq_true, List.all_eq_true]
    exact forall₂_congr fun x hx => by rw [h x hx])

theorem any_congr' {l : List Nat} {p q : Nat → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q :=
  Bool.eq_iff_iff.2 (by
    rw [List.any_eq_true, List.any_eq_true]
    exact exists_congr fun x => and_congr_right fun hx => by rw [h x hx])

theorem closed_eq {I : List Nat} (hI : ∀ y ∈ I, y < 256) :
    idxClosedOK 315 j2SylEnum I = closedK I := by
  unfold idxClosedOK closedK
  have h1 : (I.all fun y => decide (y < j2SylEnum.size)) = true := by
    rw [List.all_eq_true]
    intro y hy
    rw [size_eq]
    exact decide_eq_true (hI y hy)
  rw [h1, Bool.true_and]
  refine all_congr' fun y hy => all_congr' fun z hz => any_congr' fun t ht => ?_
  rw [get_eq (hI y hy), get_eq (hI z hz), get_eq (hI t ht),
    compT_unpack (canonT (hI y hy)) (canonT (hI z hz)),
    tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp (canonT (hI y hy)) (canonT (hI z hz))) (canonT (hI t ht))]
  rfl

theorem count_eq (I₁ I₂ : List Nat) :
    eaCountOK 315 j2Sift j2SylEnum I₁ I₂ = (List.range 256).all (countAt I₁ I₂) := by
  unfold eaCountOK centInvolIdx countAt
  rw [size_eq]
  refine all_congr' fun i hi => ?_
  rw [List.mem_range] at hi
  have hf : ((List.range 256).filter fun y => j2Sift j2SylEnum[y]! && invoOK 315 j2SylEnum[y]! &&
      commTT 315 j2SylEnum[y]! j2SylEnum[i]!) =
      (List.range 256).filter fun y => sK (T y) && invoK (T y) && commK (T y) (T i) := by
    refine List.filter_congr fun y hy => ?_
    rw [List.mem_range] at hy
    rw [get_eq hy, get_eq hi, sift_eq (canonT hy), invoOK_eq (canonT hy),
      commF (canonT hy) (canonT hi)]
  rw [hf, get_eq hi, sift_eq (canonT hi), invoOK_eq (canonT hi)]

theorem supp_eq {I₁ I₂ : List Nat} (h₁ : ∀ y ∈ I₁, y < 256) (h₂ : ∀ y ∈ I₂, y < 256) :
    eaSupportOK 315 j2Sift j2SylEnum I₁ I₂ = (List.range 256).all (suppAt I₁ I₂) := by
  unfold eaSupportOK suppAt
  rw [size_eq]
  refine all_congr' fun m hm => ?_
  rw [List.mem_range] at hm
  have hc := canonT hm
  rw [get_eq hm, sift_eq hc, involF hc]
  have key : ∀ I, (∀ y ∈ I, y < 256) →
      (!idxNormOK 315 j2SylEnum m I || twoSupportsOK 315 j2SylEnum m I) =
        (!normK m I || twoK m I) := by
    intro I hb
    unfold idxNormOK twoSupportsOK normK twoK
    have e1 : (I.all fun y => I.any fun t => tblEq 315 (compT 315 j2SylEnum[m]! j2SylEnum[y]!)
        (compT 315 j2SylEnum[t]! j2SylEnum[m]!)) =
        I.all fun y => I.any fun t => Nat.beq (pc (T m) (T y)) (pc (T t) (T m)) := by
      refine all_congr' fun y hy => any_congr' fun t ht => ?_
      rw [get_eq hm, get_eq (hb y hy), get_eq (hb t ht), compT_unpack hc (canonT (hb y hy)),
        compT_unpack (canonT (hb t ht)) hc,
        tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp hc (canonT (hb y hy))) (CFSG.KC.BfsPin.canonK_pcomp (canonT (hb t ht)) hc)]
      rfl
    have e2 : (I.any fun a => I.any fun b => commTT 315 j2SylEnum[a]! j2SylEnum[m]! &&
        commTT 315 j2SylEnum[b]! j2SylEnum[m]! && !tblEq 315 j2SylEnum[a]! (idT 315) &&
        !tblEq 315 j2SylEnum[b]! (idT 315) &&
        movedCount 315 j2SylEnum[a]! != movedCount 315 j2SylEnum[b]!) =
        I.any fun a => I.any fun b => commK (T a) (T m) && commK (T b) (T m) &&
          !Nat.beq (T a) idK && !Nat.beq (T b) idK && movK (T a) != movK (T b) := by
      refine any_congr' fun a ha => any_congr' fun b hb' => ?_
      have ca := canonT (hb a ha)
      have cb := canonT (hb b hb')
      rw [get_eq hm, get_eq (hb a ha), get_eq (hb b hb'), commF ca hc, commF cb hc, idEq ca,
        idEq cb, moved_eq ca, moved_eq cb]
    rw [e1, e2]
  simp only [List.all_cons, List.all_nil, Bool.and_true, key I₁ h₁, key I₂ h₂]

end CertificateChecks.KernelSpor.J2EA

end
