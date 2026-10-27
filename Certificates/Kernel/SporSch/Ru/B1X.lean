module

public import Certificates.Kernel.SporSch.Ru.B1W
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def anyK (n : Nat) (f : Nat → Bool) : Bool :=
  bIf(allN n (fun i => bIf(f i, false, true)), false, true)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 4060 12 (mask 12) p q

@[expose] noncomputable def x12 (j : Nat) : Bool :=
  allN 35 (fun j' => strictB (pc (XA j) (XA j')) (fun p =>
    bAnd(bIf(Nat.beq p (pidn 4060 12), true, anyK 35 (fun j'' => Nat.beq p (XA j''))),
      Nat.beq p (pc (XA j') (XA j)))))

@[expose] noncomputable def x5 (j : Nat) : Bool :=
  allN 2 (fun g => strictB (pc (pc (gen2 C0 C1 g) (XA j)) (gen2 C0I C1I g)) (fun c =>
    anyK 35 (fun j' => Nat.beq c (XA j'))))

@[expose] noncomputable def x4 (j : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight (XA j) (4060 * 12)) 0,
    siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuS4.LR RuS4.TRI RuS4.BP 2 0 (XA j))

@[expose] noncomputable def g5P : Nat := ppow 4060 12 (mask 12) (pidn 4060 12) C0 4

end CertificateChecks.KernelSporSch.RuB1K

#kss_each CertificateChecks.KernelSporSch.RuB1K.X12 CertificateChecks.KernelSporSch.RuB1K.x12 35
#kss_each CertificateChecks.KernelSporSch.RuB1K.X5 CertificateChecks.KernelSporSch.RuB1K.x5 35
#kss_each CertificateChecks.KernelSporSch.RuB1K.X4 CertificateChecks.KernelSporSch.RuB1K.x4 35

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.KC.BfsPin CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.RuB1 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.RuLines

theorem x3 : allN 35 (fun j => Nat.beq (pc (XA j) (XA j)) (pidn 4060 12)) = true := by quickRfl
theorem x6 : allN 35 (fun j => allN 35 (fun j' =>
    (!(xKept j && xKept j' && decide (j < j')) || !Nat.beq (XA j) (XA j')))) = true := by quickRfl
theorem x7 : allN 35 (fun j => !Nat.beq (XA j) (pidn 4060 12)) = true := by quickRfl
theorem x8 : allN 5 (fun k => Nat.beq (XA (Nat.mul 7 k)) Z) = true := by quickRfl
theorem x9 : Nat.beq (ppow 4060 12 (mask 12) (pidn 4060 12) C0 20) (pidn 4060 12) = true := by
  quickRfl
theorem x10 : (!Nat.beq g5P (pidn 4060 12)) = true := by quickRfl
theorem x11 : allN 35 (fun j => !Nat.beq (pc g5P (XA j)) (pc (XA j) g5P) ||
    Nat.beq (XA j) Z) = true := by quickRfl
theorem cId : canonK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) = true := by quickRfl
theorem cP : allN 5 (fun k => bAnd(canonK 4060 12 (mask 12) (4060 * 12)
    (ppow 4060 12 (mask 12) (pidn 4060 12) C0 k), canonK 4060 12 (mask 12) (4060 * 12)
    (ppow 4060 12 (mask 12) (pidn 4060 12) C0I k))) = true := by quickRfl
theorem cP20 : canonK 4060 12 (mask 12) (4060 * 12)
    (ppow 4060 12 (mask 12) (pidn 4060 12) C0 20) = true := by quickRfl
theorem cG5 : canonK 4060 12 (mask 12) (4060 * 12) g5P = true := by quickRfl
theorem cC1I : canonK 4060 12 (mask 12) (4060 * 12) C1I = true := by quickRfl

theorem anyK_spec {n : Nat} {f : Nat → Bool} (h : anyK n f = true) : ∃ i < n, f i = true := by
  by_contra hne
  have ha : allN n (fun i => bIf(f i, false, true)) = true :=
    allN_of_forall fun i hi => by
      cases e : f i
      · rfl
      · exact absurd ⟨i, hi, e⟩ hne
  unfold anyK at h
  rw [ha] at h
  exact Bool.false_ne_true h

theorem nat_any_of {n : Nat} {f : Nat → Bool} {i : Nat} (hi : i < n) (h : f i = true) :
    (Nat.any n fun k _ => f k) = true := by
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  exact ⟨⟨i, hi⟩, List.mem_finRange _, h⟩

theorem cX' {j : Nat} (hj : j < 35) : canonK 4060 12 (mask 12) (4060 * 12) (XA j) = true :=
  allN_spec cX j hj

theorem idA_eq : idA 4060 = unpack 4060 12 (pidn 4060 12) := (idK_sound idOK).symm

theorem pow_eq {p e : Nat} (hc : canonK 4060 12 (mask 12) (4060 * 12) p = true) :
    powA 4060 (unpack 4060 12 p) e = unpack 4060 12 (ppow 4060 12 (mask 12) (pidn 4060 12) p e) :=
  powEqRK_sound (by rw [powEqRK, hc]; exact Nat.beq_refl _)

theorem eqA_canon {p q : Nat} (hp : canonK 4060 12 (mask 12) (4060 * 12) p = true)
    (hq : canonK 4060 12 (mask 12) (4060 * 12) q = true) :
    eqA 4060 (unpack 4060 12 p) (unpack 4060 12 q) = Nat.beq p q := eqA_unpack hp hq

theorem c0i_eq : ruInv ruC0A = unpack 4060 12 C0I := (inv_of c0_eq pC0).1

theorem xl_eq {j : Nat} (hj : j < 35) : xList[j]! = unpack 4060 12 (XA j) := by
  have hk := allN_spec cP (j / 7) (by omega)
  obtain ⟨hk1, hk2⟩ := (bAnd_iff _ _).1 hk
  have he := allN_spec cE (j % 7) (by omega)
  rw [xList, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, xArr,
    RuB1K.e_eq (by omega), c0_eq, pow_eq RuCe.cC0, ← c0_eq, c0i_eq, pow_eq cC0I,
    compA_unpack hk1 he, compA_unpack (canonK_pcomp hk1 he) hk2,
    ← Nat.eq_of_beq_eq_true (allN_spec xOK j hj)]
  rfl

theorem prod_eq {j j' : Nat} (hj : j < 35) (hj' : j' < 35) :
    compA 4060 xList[j]! xList[j']! = unpack 4060 12 (pc (XA j) (XA j')) := by
  rw [xl_eq hj, xl_eq hj', compA_unpack (cX' hj) (cX' hj')]
  rfl

theorem cpc {j j' : Nat} (hj : j < 35) (hj' : j' < 35) :
    canonK 4060 12 (mask 12) (4060 * 12) (pc (XA j) (XA j')) = true :=
  canonK_pcomp (cX' hj) (cX' hj')

theorem g5_eq : g5A = unpack 4060 12 g5P := by
  rw [g5A, c0_eq, pow_eq RuCe.cC0]
  rfl

theorem sb_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bindsS4 : Binds 4060 12 RuS4.S 6 2 RuS4.BP (ruField4060 4)
    (ruBaseArr 4060 ruS4060ChainBase) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, by simp [ruBaseArr,
    ruS4060ChainBase], fun t ht => Nat.eq_of_beq_eq_true (allN_spec RuS4M.baseOK t ht)⟩
  · rw [ruField4060, Array.size_ofFn]
    rfl
  · have e : RuS4.S j = RuT4060.L (Nat.add 33 j) := Nat.eq_of_beq_eq_true (allN_spec RuS4M.sOK j hj)
    rw [RuCe.f4060 33 6 (33 + j) rfl hj rfl (by omega)]
    exact congrArg (unpack 4060 12) e.symm

theorem conj_eq {g j : Nat} (hg : g < 2) (hj : j < 35) :
    ruConjA #[ruC0A, ruC1A][g]! xList[j]! =
      unpack 4060 12 (pc (pc (gen2 C0 C1 g) (XA j)) (gen2 C0I C1I g)) := by
  have hc : canonK 4060 12 (mask 12) (4060 * 12) (gen2 C0 C1 g) = true ∧
      canonK 4060 12 (mask 12) (4060 * 12) (gen2 C0I C1I g) = true ∧
      invCand 4060 #[ruC0A, ruC1A][g]! = unpack 4060 12 (gen2 C0I C1I g) := by
    rcases g with _ | _ | g
    · exact ⟨RuCe.cC0, cC0I, c0i_eq⟩
    · exact ⟨RuCe.cC1, cC1I, (inv_of c1_eq pC1).1⟩
    · omega
  obtain ⟨h1, h2, h3⟩ := hc
  rw [ruConjA, h3, (binds2 c0_eq c1_eq).2 g hg, xl_eq hj, compA_unpack h1 (cX' hj),
    compA_unpack (canonK_pcomp h1 (cX' hj)) h2]
  rfl

theorem xCheck : ruB1XCheck = true := by
  unfold ruB1XCheck xCheckWith
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨fun j hj j' hj' => ?_, fun j hj j' hj' => ?_⟩, fun j hj => ?_⟩, fun j hj => ?_⟩,
    fun j hj g hg => ?_⟩, fun j hj j' hj' => ?_⟩, fun j hj => ?_⟩, fun k hk => ?_⟩, ?_⟩, ?_⟩,
    fun j hj => ?_⟩
  · have h := allN_spec (X12.all j hj) j' hj'
    rw [sb_eq] at h
    obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 h
    rw [prod_eq hj hj', idA_eq, eqA_canon (cpc hj hj') cId]
    cases e : Nat.beq (pc (XA j) (XA j')) (pidn 4060 12)
    · rw [e] at h1
      obtain ⟨j'', hj'', h3⟩ := anyK_spec h1
      rw [Bool.false_or]
      refine nat_any_of hj'' ?_
      rw [xl_eq hj'', eqA_canon (cpc hj hj') (cX' hj''), h3]
    · rfl
  · have h := allN_spec (X12.all j hj) j' hj'
    rw [sb_eq] at h
    obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
    rw [prod_eq hj hj', prod_eq hj' hj, eqA_canon (cpc hj hj') (cpc hj' hj), h2]
  · rw [prod_eq hj hj, idA_eq, eqA_canon (cpc hj hj) cId]
    exact allN_spec x3 j hj
  · obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 (X4.all j hj)
    exact siftK_sound bindsS4 RuS4M.perm RuS4.hl (xl_eq hj) (range_of_canonK (cX' hj)) h2
  · have h := allN_spec (X5.all j hj) g hg
    rw [sb_eq] at h
    obtain ⟨j', hj', h3⟩ := anyK_spec h
    refine nat_any_of hj' ?_
    have hc : canonK 4060 12 (mask 12) (4060 * 12)
        (pc (pc (gen2 C0 C1 g) (XA j)) (gen2 C0I C1I g)) = true := by
      rcases g with _ | _ | g
      · exact canonK_pcomp (canonK_pcomp RuCe.cC0 (cX' hj)) cC0I
      · exact canonK_pcomp (canonK_pcomp RuCe.cC1 (cX' hj)) cC1I
      · omega
    rw [conj_eq hg hj, xl_eq hj', eqA_canon hc (cX' hj'), h3]
  · rw [xl_eq hj, xl_eq hj', eqA_canon (cX' hj) (cX' hj')]
    exact allN_spec (allN_spec x6 j hj) j' hj'
  · rw [xl_eq hj, idA_eq, eqA_canon (cX' hj) cId]
    exact allN_spec x7 j hj
  · rw [xl_eq (by omega), z_eq, eqA_canon (cX' (by omega)) RuF.zCanon]
    exact allN_spec x8 k hk
  · rw [c0_eq, pow_eq RuCe.cC0, idA_eq, eqA_canon cP20 cId]
    exact x9
  · rw [g5_eq, idA_eq, eqA_canon cG5 cId]
    exact x10
  · rw [g5_eq, xl_eq hj, compA_unpack cG5 (cX' hj), compA_unpack (cX' hj) cG5,
      eqA_canon (canonK_pcomp cG5 (cX' hj)) (canonK_pcomp (cX' hj) cG5), z_eq,
      eqA_canon (cX' hj) RuF.zCanon]
    exact allN_spec x11 j hj

end CertificateChecks.KernelSporSch.RuB1K

end
