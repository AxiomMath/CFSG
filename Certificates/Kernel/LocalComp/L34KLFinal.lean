
module

public import Certificates.Kernel.LocalComp.L34KLChk
public import Certificates.Kernel.LocalComp.L34N3Final
public import CFSG.Certificates.Kernel.L34KLWSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAKL34SpecBase
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34KL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CFSG.KC.L34KLW CFSG.KC.L34KSnd CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four
open CFSG.RankThree.PartTwo.Sec21.FF79.KL34 (mem_closure_pair_pow pow_eq_pow_mod_three)
open CFSG.KLie.CT (andB orB notB)

theorem canonS {j : Nat} (hj : j < 20160) : canonK 42 6 (mask 6) (42 * 6) (L34S.T j) = true :=
  pinS.canon j hj

theorem S_mem {j : Nat} (hj : j < 20160) : ∃ g ∈ S, TabRep (unpack 42 6 (L34S.T j)) g := by
  have hE : Enumerates S (pts 42 6 20160 L34S.T).toList := by
    have h := enumerates_S
    rwa [enumS, hS.1] at h
  obtain ⟨g, hg, r⟩ := hE.sound _ (getElem!_mem (by rw [size_pts]; exact hj))
  have e : (pts 42 6 20160 L34S.T)[j]! = unpack 42 6 (L34S.T j) := pts_get hj
  rw [e] at r
  exact ⟨g, hg, r⟩

theorem e9_get {k : Nat} (hk : k < 9) :
    (e9T ())[k]! = comp 42 (powTab 42 a₀T (k / 3)) (powTab 42 b₀T (k % 3)) := by
  unfold e9T
  rw [getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]

theorem a₀_facts : ∃ a ∈ S, ∃ b ∈ S, TabRep a₀T a ∧ TabRep b₀T b ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
    a * b = b * a ∧
    ∀ k < 9, ∀ k' < 9, a ^ (k / 3) * b ^ (k % 3) = a ^ (k' / 3) * b ^ (k' % 3) → k = k' := by
  obtain ⟨hA1, hA2⟩ := andB_iff.1 kA
  obtain ⟨hl0, hl1⟩ := andB_iff.1 hA1
  obtain ⟨he0, he1⟩ := andB_iff.1 hA2
  obtain ⟨a, haS, ra⟩ := S_mem (Nat.blt_eq.mp hl0)
  obtain ⟨b, hbS, rb⟩ := S_mem (Nat.blt_eq.mp hl1)
  rw [Nat.eq_of_beq_eq_true he0, L34N.K_tabs.1] at ra
  rw [Nat.eq_of_beq_eq_true he1, L34N.K_tabs.2.1] at rb
  obtain ⟨h1, h2⟩ := andB_iff.1 kAB
  obtain ⟨h3a, h3b⟩ := andB_iff.1 h1
  obtain ⟨hc, hd⟩ := andB_iff.1 h2
  have c0 := L34N.canonK' (j := 0) (by decide)
  have c1 := L34N.canonK' (j := 1) (by decide)
  have ha3 := ((o3Pt_iff c0).1 h3a).2
  have hb3 := ((o3Pt_iff c1).1 h3b).2
  have hab := (commPt_iff c0 c1).1 hc
  rw [L34N.K_tabs.1] at ha3 hab
  rw [L34N.K_tabs.2.1] at hb3 hab
  have hrepE : ∀ k < 9, TabRep (e9T ())[k]! (a ^ (k / 3) * b ^ (k % 3)) := fun k hk => by
    rw [e9_get hk]
    exact (ra.pow _).comp (rb.pow _)
  refine ⟨a, haS, b, hbS, ra, rb, ?_, ?_, ((ra.comp rb).eq_iff (rb.comp ra)).1 hab, ?_⟩
  · rw [pow_three]
    exact ((ra.comp (ra.comp ra)).eq_iff TabRep.idTab).1 ha3
  · rw [pow_three]
    exact ((rb.comp (rb.comp rb)).eq_iff TabRep.idTab).1 hb3
  · intro k hk k' hk' he
    have e := ((hrepE k hk).eq_iff (hrepE k' hk')).2 he
    rw [← L34N.K_tabs.2.2.2 k hk, ← L34N.K_tabs.2.2.2 k' hk'] at e
    have e' := unpack_inj' (L34N.canonAP hk) (L34N.canonAP hk') e
    have hkk := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hd k hk) k' hk'
    rcases orB_iff.1 hkk with h | h
    · exact Nat.eq_of_beq_eq_true h
    · rw [notB_iff, e', Nat.beq_refl] at h
      exact Bool.noConfusion h

theorem A₀_spec {a b : Equiv.Perm (Fin 42)} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a)
    (hinj : ∀ k < 9, ∀ k' < 9, a ^ (k / 3) * b ^ (k % 3) = a ^ (k' / 3) * b ^ (k' % 3) → k = k') :
    Nat.card (Subgroup.closure {a, b}) = 9 ∧
      ∀ x ∈ Subgroup.closure {a, b}, ∃ k < 9, x = a ^ (k / 3) * b ^ (k % 3) := by
  have hform : ∀ x ∈ Subgroup.closure {a, b}, ∃ k < 9, x = a ^ (k / 3) * b ^ (k % 3) := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := mem_closure_pair_pow hab ha3 hb3 hx
    refine ⟨3 * (i % 3) + j % 3, by omega, ?_⟩
    have e1 : (3 * (i % 3) + j % 3) / 3 = i % 3 := by omega
    have e2 : (3 * (i % 3) + j % 3) % 3 = j % 3 := by omega
    rw [e1, e2, ← pow_eq_pow_mod_three ha3, ← pow_eq_pow_mod_three hb3]
  refine ⟨?_, hform⟩
  have haA : a ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (Or.inl rfl)
  have hbA : b ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (Or.inr rfl)
  have hrange : ((Subgroup.closure {a, b} : Subgroup (Equiv.Perm (Fin 42))) :
      Set (Equiv.Perm (Fin 42))) = Set.range (fun k : Fin 9 => a ^ (k.val / 3) * b ^ (k.val % 3)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, rfl⟩ := hform x hx
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact (Subgroup.closure {a, b}).mul_mem ((Subgroup.closure {a, b}).pow_mem haA _)
        ((Subgroup.closure {a, b}).pow_mem hbA _)
  have hf : Function.Injective (fun k : Fin 9 => a ^ (k.val / 3) * b ^ (k.val % 3)) :=
    fun k k' he => Fin.ext (hinj k.val k.2 k'.val k'.2 he)
  calc Nat.card (Subgroup.closure {a, b}) =
        Nat.card ((Subgroup.closure {a, b} : Subgroup (Equiv.Perm (Fin 42))) :
          Set (Equiv.Perm (Fin 42))) := rfl
    _ = Nat.card (Set.range (fun k : Fin 9 => a ^ (k.val / 3) * b ^ (k.val % 3))) := by
      rw [hrange]
    _ = Nat.card (Fin 9) := Nat.card_range_of_injective hf
    _ = 9 := by simp

theorem norm_tabs {a b x : Equiv.Perm (Fin 42)} {X : Tab} (ra : TabRep a₀T a) (rb : TabRep b₀T b)
    (hrepE : ∀ k < 9, TabRep (e9T ())[k]! (a ^ (k / 3) * b ^ (k % 3)))
    (hform : ∀ y ∈ Subgroup.closure {a, b}, ∃ k < 9, y = a ^ (k / 3) * b ^ (k % 3))
    (hx : TabRep X x) (hn : ∀ c ∈ Subgroup.closure {a, b}, x * c * x⁻¹ ∈ Subgroup.closure {a, b}) :
    (∃ j < 9, comp 42 X a₀T = comp 42 (e9T ())[j]! X) ∧
      (∃ j < 9, comp 42 X b₀T = comp 42 (e9T ())[j]! X) := by
  have hex : ∀ c ∈ Subgroup.closure {a, b}, ∃ i < 9, x * c = (a ^ (i / 3) * b ^ (i % 3)) * x := by
    intro c hc
    obtain ⟨i, hi, hie⟩ := hform _ (hn c hc)
    exact ⟨i, hi, mul_inv_eq_iff_eq_mul.1 hie⟩
  obtain ⟨ia, hia, hiae⟩ := hex a (Subgroup.subset_closure (Or.inl rfl))
  obtain ⟨ib, hib, hibe⟩ := hex b (Subgroup.subset_closure (Or.inr rfl))
  exact ⟨⟨ia, hia, ((hx.comp ra).eq_iff ((hrepE ia hia).comp hx)).2 hiae⟩,
    ⟨ib, hib, ((hx.comp rb).eq_iff ((hrepE ib hib).comp hx)).2 hibe⟩⟩

theorem kW_at {q : Nat} (hq : q < 7755) :
    klEnt 42 6 9 L34N.AP (pidn 42 6) (L34N.K 0) (L34N.K 1) L34R.T 24 Q
      (fun j => L34S.T (QS j)) (fun j => L34S.T (TS j)) q (L34N.J q) = true := by
  have h := kW
  unfold wit at h
  rw [strictB_eq] at h
  exact CFSG.KS.Raw.Orb.allN_iff.1 h q hq

theorem listed_of {a b x : Equiv.Perm (Fin 42)} (ra : TabRep a₀T a) (rb : TabRep b₀T b)
    (hrepE : ∀ k < 9, TabRep (e9T ())[k]! (a ^ (k / 3) * b ^ (k % 3)))
    (hform : ∀ y ∈ Subgroup.closure {a, b}, ∃ k < 9, y = a ^ (k / 3) * b ^ (k % 3))
    (hxR : x ∈ R) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxn : ∀ c ∈ Subgroup.closure {a, b}, x * c * x⁻¹ ∈ Subgroup.closure {a, b})
    (hx60 : 60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
      Subgroup (Equiv.Perm (Fin 42)))) :
    ∃ q < 7755, TabRep (unpack 42 6 (L34R.T (L34N.J q / 32))) x ∧ L34N.J q % 2 = 1 ∧
      L34N.J q % 32 / 8 = 3 := by
  obtain ⟨i, hi, ht⟩ := L34N3.exists_T hxR
  have h1' : unpack 42 6 (L34R.T i) ≠ idTab 42 := fun e => hx1 ((ht.eq_iff TabRep.idTab).1 e)
  have h3' : comp 42 (unpack 42 6 (L34R.T i)) (comp 42 (unpack 42 6 (L34R.T i))
      (unpack 42 6 (L34R.T i))) = idTab 42 :=
    ((ht.comp (ht.comp ht)).eq_iff TabRep.idTab).2 (by rw [← pow_three]; exact hx3)
  have hf : L34N.nfix (unpack 42 6 (L34R.T i)) = 6 * 2 := by
    rw [L34N3.nfix_eq ht]
    rcases L34N3.card_centS_of_order3 hxR hx3 hx1 with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · omega
    · exact h
  obtain ⟨q', hq', hq'i, hq'c⟩ := (L34N.order3_iff hi (c := 2) (by decide)).1 ⟨h1', h3', hf⟩
  obtain ⟨q, hq, hqi, hqo⟩ := (L34N.normA_iff hi).1 (norm_tabs ra rb hrepE hform ht hxn)
  obtain ⟨k, -, -, -, hk32, hkJ⟩ := L34N.listed.get q (Nat.zero_le _) hq
  obtain ⟨k', -, -, -, hk32', hkJ'⟩ := L34N.listed.get q' (Nat.zero_le _) hq'
  have hk : k = i := by omega
  have hk' : k' = i := by omega
  subst hk hk'
  refine ⟨q, hq, by rw [hqi]; exact ht, hqo, by omega⟩

theorem c0 : canonK 42 6 (mask 6) (42 * 6) (L34N.K 0) = true := L34N.canonK' (j := 0) (by decide)

theorem c1 : canonK 42 6 (mask 6) (42 * 6) (L34N.K 1) = true := L34N.canonK' (j := 1) (by decide)

theorem norm_of {a b y : Equiv.Perm (Fin 42)} {Yp : Nat} (ra : TabRep a₀T a) (rb : TabRep b₀T b)
    (hrepE : ∀ k < 9, TabRep (e9T ())[k]! (a ^ (k / 3) * b ^ (k % 3)))
    (hY : canonK 42 6 (mask 6) (42 * 6) Yp = true) (ry : TabRep (unpack 42 6 Yp) y)
    (hia : inPts 42 6 9 L34N.AP Yp (L34N.K 0) = true)
    (hib : inPts 42 6 9 L34N.AP Yp (L34N.K 1) = true) :
    ∀ c ∈ Subgroup.closure {a, b}, y * c * y⁻¹ ∈ Subgroup.closure {a, b} := by
  have hmemE : ∀ k, a ^ (k / 3) * b ^ (k % 3) ∈ Subgroup.closure {a, b} := fun k =>
    (Subgroup.closure {a, b}).mul_mem
      ((Subgroup.closure {a, b}).pow_mem (Subgroup.subset_closure (Or.inl rfl)) _)
      ((Subgroup.closure {a, b}).pow_mem (Subgroup.subset_closure (Or.inr rfl)) _)
  have one : ∀ {g : Equiv.Perm (Fin 42)} {gT : Tab} {i : Nat}, TabRep gT g → unpack 42 6 (L34N.K i) = gT →
      canonK 42 6 (mask 6) (42 * 6) (L34N.K i) = true →
      inPts 42 6 9 L34N.AP Yp (L34N.K i) = true → y * g * y⁻¹ ∈ Subgroup.closure {a, b} := by
    intro g gT i rg eg cg h
    obtain ⟨j, hj, e⟩ := (inPts_iff hY cg fun j hj => L34N.canonAP hj).1 h
    rw [eg, L34N.K_tabs.2.2.2 j hj] at e
    rw [mul_inv_eq_iff_eq_mul.2 (((ry.comp rg).eq_iff ((hrepE j hj).comp ry)).1 e)]
    exact hmemE j
  have e1 := one ra L34N.K_tabs.1 c0 hia
  have e2 := one rb L34N.K_tabs.2.1 c1 hib
  have hle : Subgroup.closure {a, b} ≤
      (Subgroup.closure {a, b}).comap (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [e1, e2]
  exact fun c hc => hle hc

theorem q_of {a b x y : Equiv.Perm (Fin 42)} {Xp Yp : Nat} (ra : TabRep a₀T a) (rb : TabRep b₀T b)
    (hrepE : ∀ k < 9, TabRep (e9T ())[k]! (a ^ (k / 3) * b ^ (k % 3)))
    (hX : canonK 42 6 (mask 6) (42 * 6) Xp = true) (hY : canonK 42 6 (mask 6) (42 * 6) Yp = true)
    (rx : TabRep (unpack 42 6 Xp) x) (ry : TabRep (unpack 42 6 Yp) y)
    (h : q4Pt 42 6 9 L34N.AP (L34N.K 0) (L34N.K 1) Xp Yp = true) :
    (∀ c ∈ Subgroup.closure {a, b}, y * c * y⁻¹ ∈ Subgroup.closure {a, b}) ∧ y ^ 4 = 1 ∧
      y ^ 2 ≠ 1 ∧ x * y ^ 2 = y ^ 2 * x := by
  unfold q4Pt at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  obtain ⟨hia, hib⟩ := andB_iff.1 h1
  obtain ⟨h3, hc⟩ := andB_iff.1 h2
  obtain ⟨h4, hn2⟩ := andB_iff.1 h3
  refine ⟨norm_of ra rb hrepE hY ry hia hib, ?_, fun e => ?_, ?_⟩
  · have e := ((ry.comp (ry.comp (ry.comp ry))).eq_iff TabRep.idTab).1 ((o4Pt_iff hY).1 h4)
    rw [← e, pow_succ', pow_succ', pow_two]
  · have e' : invPt 42 6 Yp = true := (invPt_iff hY).2
      (((ry.comp ry).eq_iff TabRep.idTab).2 (by rw [← sq]; exact e))
    rw [notB_iff, e'] at hn2
    exact Bool.noConfusion hn2
  · have e := ((rx.comp (ry.comp ry)).eq_iff (ry.comp (ry.comp rx))).1 ((comm2Pt_iff hX hY).1 hc)
    rw [sq, e, ← mul_assoc]

theorem tau_of {a b x t : Equiv.Perm (Fin 42)} {Xp Tp : Nat} (ra : TabRep a₀T a)
    (rb : TabRep b₀T b) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hform : ∀ y ∈ Subgroup.closure {a, b}, ∃ k < 9, y = a ^ (k / 3) * b ^ (k % 3))
    (hX : canonK 42 6 (mask 6) (42 * 6) Xp = true) (hT : canonK 42 6 (mask 6) (42 * 6) Tp = true)
    (rx : TabRep (unpack 42 6 Xp) x) (rt : TabRep (unpack 42 6 Tp) t)
    (h : tauPt 42 6 (pidn 42 6) (L34N.K 0) (L34N.K 1) Xp Tp = true) :
    t ^ 2 = 1 ∧ t ≠ 1 ∧ (∀ c ∈ Subgroup.closure {a, b}, t * c * t⁻¹ = c⁻¹) ∧ x * t = t * x := by
  unfold tauPt at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  obtain ⟨hi2, hne⟩ := andB_iff.1 h1
  obtain ⟨h3, hc⟩ := andB_iff.1 h2
  obtain ⟨hta, htb⟩ := andB_iff.1 h3
  have inv1 : ∀ {g : Equiv.Perm (Fin 42)} {gT : Tab} {i : Nat}, TabRep gT g → g ^ 3 = 1 →
      unpack 42 6 (L34N.K i) = gT → canonK 42 6 (mask 6) (42 * 6) (L34N.K i) = true →
      invAPt 42 6 Tp (L34N.K i) = true → t * g * t⁻¹ = g⁻¹ := by
    intro g gT i rg hg3 eg cg hi
    have e := (invAPt_iff hT cg).1 hi
    rw [eg] at e
    have e' := ((rt.comp rg).eq_iff (rg.comp (rg.comp rt))).1 e
    rw [mul_inv_eq_iff_eq_mul, e', ← mul_assoc]
    congr 1
    rw [eq_inv_iff_mul_eq_one, ← hg3, pow_three, mul_assoc]
  have h1a := inv1 ra ha3 L34N.K_tabs.1 c0 hta
  have h1b := inv1 rb hb3 L34N.K_tabs.2.1 c1 htb
  refine ⟨?_, fun e => ?_, fun c hc => ?_, ?_⟩
  · rw [sq]
    exact ((rt.comp rt).eq_iff TabRep.idTab).1 ((invPt_iff hT).1 hi2)
  · have e' := (unpack_eq_idTab_iff hT).1 ((rt.eq_iff TabRep.idTab).2 e)
    rw [notB_iff, e', Nat.beq_refl] at hne
    exact Bool.noConfusion hne
  · obtain ⟨k, -, rfl⟩ := hform c hc
    have e1 : t * a ^ (k / 3) * t⁻¹ = (a ^ (k / 3))⁻¹ := by rw [← conj_pow, h1a, inv_pow]
    have e2 : t * b ^ (k % 3) * t⁻¹ = (b ^ (k % 3))⁻¹ := by rw [← conj_pow, h1b, inv_pow]
    have hcm : Commute (a ^ (k / 3)) (b ^ (k % 3)) := (show Commute a b from hab).pow_pow _ _
    calc t * (a ^ (k / 3) * b ^ (k % 3)) * t⁻¹
        = (t * a ^ (k / 3) * t⁻¹) * (t * b ^ (k % 3) * t⁻¹) := by group
      _ = (a ^ (k / 3))⁻¹ * (b ^ (k % 3))⁻¹ := by rw [e1, e2]
      _ = (b ^ (k % 3) * a ^ (k / 3))⁻¹ := by rw [mul_inv_rev]
      _ = (a ^ (k / 3) * b ^ (k % 3))⁻¹ := by rw [hcm.eq]
  · exact ((rx.comp rt).eq_iff (rt.comp rx)).1 ((commPt_iff hX hT).1 hc)

theorem rep_one : TabRep (unpack 42 6 (pidn 42 6)) (1 : Equiv.Perm (Fin 42)) := by
  rw [← idTab_unpack' (canon_sz c0)]
  exact TabRep.idTab

theorem canon_one : canonK 42 6 (mask 6) (42 * 6) (pidn 42 6) = true := canon_pidn (canon_sz c0)

theorem wit_of {a b x : Equiv.Perm (Fin 42)} (ra : TabRep a₀T a) (rb : TabRep b₀T b)
    (hrepE : ∀ k < 9, TabRep (e9T ())[k]! (a ^ (k / 3) * b ^ (k % 3)))
    (hform : ∀ y ∈ Subgroup.closure {a, b}, ∃ k < 9, y = a ^ (k / 3) * b ^ (k % 3))
    (hxR : x ∈ R) (hx3 : x ^ 3 = 1)
    (hxn : ∀ c ∈ Subgroup.closure {a, b}, x * c * x⁻¹ ∈ Subgroup.closure {a, b})
    (hx60 : 60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
      Subgroup (Equiv.Perm (Fin 42)))) :
    ∃ Xp, ∃ j < 24, canonK 42 6 (mask 6) (42 * 6) Xp = true ∧ TabRep (unpack 42 6 Xp) x ∧
      q4Pt 42 6 9 L34N.AP (L34N.K 0) (L34N.K 1) Xp (L34S.T (QS j)) = true ∧
      tauPt 42 6 (pidn 42 6) (L34N.K 0) (L34N.K 1) Xp (L34S.T (TS j)) = true := by
  by_cases hx1 : x = 1
  · subst hx1
    have h := kOne
    rw [strictB_eq] at h
    obtain ⟨h1, h2⟩ := andB_iff.1 h
    exact ⟨pidn 42 6, 0, by decide, canon_one, rep_one, h1, h2⟩
  · obtain ⟨q, hq, rx, hqo, hq3⟩ := listed_of ra rb hrepE hform hxR hx3 hx1 hxn hx60
    obtain ⟨-, h⟩ := klEnt_spec (kW_at hq) hqo
    obtain ⟨j, hj, -, h1, h2⟩ := h hq3
    obtain ⟨k, -, hk, -, hk32, hkJ⟩ := L34N.listed.get q (Nat.zero_le _) hq
    exact ⟨_, j, hj, L34N.canonT (by omega), rx, h1, h2⟩

theorem facts799525 :
    ∃ A₀ : Subgroup (Equiv.Perm (Fin 42)), A₀ ≤ S ∧ Nat.card A₀ = 9 ∧
      (∀ x ∈ R, (∀ a ∈ A₀, x * a = a * x) → x ^ 4 = 1 → x ^ 2 = 1) ∧
      (∀ x ∈ R, x ^ 3 = 1 → (∀ a ∈ A₀, x * a * x⁻¹ ∈ A₀) →
        60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
          Subgroup (Equiv.Perm (Fin 42))) →
        ∃ q ∈ S, (∀ a ∈ A₀, q * a * q⁻¹ ∈ A₀) ∧ q ^ 4 = 1 ∧ q ^ 2 ≠ 1 ∧
          x * q ^ 2 = q ^ 2 * x) := by
  obtain ⟨a, haS, b, hbS, ra, rb, ha3, hb3, hab, hinj⟩ := a₀_facts
  have hrepE : ∀ k < 9, TabRep (e9T ())[k]! (a ^ (k / 3) * b ^ (k % 3)) := fun k hk => by
    rw [e9_get hk]
    exact (ra.pow _).comp (rb.pow _)
  obtain ⟨hcard, hform⟩ := A₀_spec ha3 hb3 hab hinj
  have haA : a ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (Or.inl rfl)
  have hbA : b ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (Or.inr rfl)
  refine ⟨Subgroup.closure {a, b}, (Subgroup.closure_le S).2 ?_, hcard, ?_, ?_⟩
  · rintro _ (rfl | rfl)
    exacts [haS, hbS]
  · intro x hxR hxc hx4
    obtain ⟨i, hi, ht⟩ := L34N3.exists_T hxR
    have hxn : ∀ c ∈ Subgroup.closure {a, b}, x * c * x⁻¹ ∈ Subgroup.closure {a, b} := by
      intro c hc
      rw [hxc c hc, mul_inv_cancel_right]
      exact hc
    obtain ⟨q, hq, hqi, hqo⟩ := (L34N.normA_iff hi).1 (norm_tabs ra rb hrepE hform ht hxn)
    have h := (klEnt_spec (kW_at hq) hqo).1
    rw [hqi] at h
    unfold c4Pt at h
    have cT := L34N.canonT hi
    have hca : commPt 42 6 (L34R.T i) (L34N.K 0) = true := by
      rw [commPt_iff cT c0, L34N.K_tabs.1]
      exact ((ht.comp ra).eq_iff (ra.comp ht)).2 (hxc a haA)
    have hcb : commPt 42 6 (L34R.T i) (L34N.K 1) = true := by
      rw [commPt_iff cT c1, L34N.K_tabs.2.1]
      exact ((ht.comp rb).eq_iff (rb.comp ht)).2 (hxc b hbA)
    have h4 : o4Pt 42 6 (L34R.T i) = true := by
      rw [o4Pt_iff cT]
      exact ((ht.comp (ht.comp (ht.comp ht))).eq_iff TabRep.idTab).2 (by rw [← hx4, pow_succ', pow_succ', pow_two])
    rw [hca, hcb, h4] at h
    rcases orB_iff.1 h with h' | h'
    · exact absurd h' (by decide)
    · rw [sq]
      exact ((ht.comp ht).eq_iff TabRep.idTab).1 ((invPt_iff cT).1 h')
  · intro x hxR hx3 hxn hx60
    obtain ⟨Xp, j, hj, hX, rx, h1, -⟩ := wit_of ra rb hrepE hform hxR hx3 hxn hx60
    obtain ⟨hb1, -⟩ := andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 kWB j hj)
    have hjS := Nat.blt_eq.mp hb1
    obtain ⟨y, hyS, ry⟩ := S_mem hjS
    exact ⟨y, hyS, q_of ra rb hrepE hX (canonS hjS) rx ry h1⟩

theorem facts799526 :
    ∃ A₀ : Subgroup (Equiv.Perm (Fin 42)), A₀ ≤ S ∧ Nat.card A₀ = 9 ∧
      (∀ x ∈ R, x ^ 3 = 1 → (∀ a ∈ A₀, x * a * x⁻¹ ∈ A₀) →
        60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
          Subgroup (Equiv.Perm (Fin 42))) →
        ∃ τ ∈ S, τ ^ 2 = 1 ∧ τ ≠ 1 ∧ (∀ a ∈ A₀, τ * a * τ⁻¹ = a⁻¹) ∧ x * τ = τ * x) ∧
      (∀ x ∈ R, x ∉ S → x ^ 3 = 1 →
        60 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
          Subgroup (Equiv.Perm (Fin 42))) →
        Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S :
          Subgroup (Equiv.Perm (Fin 42))) = 60) := by
  obtain ⟨a, haS, b, hbS, ra, rb, ha3, hb3, hab, hinj⟩ := a₀_facts
  have hrepE : ∀ k < 9, TabRep (e9T ())[k]! (a ^ (k / 3) * b ^ (k % 3)) := fun k hk => by
    rw [e9_get hk]
    exact (ra.pow _).comp (rb.pow _)
  obtain ⟨hcard, hform⟩ := A₀_spec ha3 hb3 hab hinj
  refine ⟨Subgroup.closure {a, b}, (Subgroup.closure_le S).2 ?_, hcard, ?_, ?_⟩
  · rintro _ (rfl | rfl)
    exacts [haS, hbS]
  · intro x hxR hx3 hxn hx60
    obtain ⟨Xp, j, hj, hX, rx, -, h2⟩ := wit_of ra rb hrepE hform hxR hx3 hxn hx60
    obtain ⟨-, hb2⟩ := andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 kWB j hj)
    have hjS := Nat.blt_eq.mp hb2
    obtain ⟨t, htS, rt⟩ := S_mem hjS
    exact ⟨t, htS, tau_of ra rb ha3 hb3 hab hform hX (canonS hjS) rx rt h2⟩
  · intro x hxR hxS hx3 hx60
    have hx1 : x ≠ 1 := fun e => hxS (e ▸ S.one_mem)
    rcases L34N3.card_centS_of_order3 hxR hx3 hx1 with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · omega
    · omega
    · exact h

end CertificateChecks.KernelLC.L34KL

end
