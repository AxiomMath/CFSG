module

public import Certificates.Kernel.U43Twin.WFacts
public import Certificates.Kernel.U43Twin.SPts
public import CFSG.Certificates.Kernel.U43Twin.SSound
import Certificates.Kernel.U43Pk.Facts
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.PackSetSound
public import Std.Tactic.BVDecide.Normalize.Bool

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Twin

open CFSG.KD.U43Pk CFSG.KD.U43Twin CFSG.KS.U43Pk CFSG.KS.U43Twin
open CFSG.Monster.B.Fischer CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
open Certificates.U43Twin

@[expose] noncomputable def SQ (v : ℕ) : ℕ × ℕ × ℕ × ℕ := (SQK v / 27, SQK v / 9 % 3, SQK v / 3 % 3, SQK v % 3)

theorem slPin : slQuads = (List.range 24).map SQ := by decide +kernel

theorem psiV : ∀ v < 24, psiTab[qidx (SQ v)]! = dec (L2 v) := by decide +kernel

theorem mtPin : ∀ a < 24, ∀ b < 24,
    MT a b < 24 ∧ qidx (qmul (SQ a) (SQ b)) = qidx (SQ (MT a b)) := by decide +kernel

theorem psiShape : ∀ v < 24, innerShape psiTab[qidx (SQ v)]! = true ∧
    (SQ v == (1, 0, 0, 1) || !isZ psiTab[qidx (SQ v)]!) = true := by decide +kernel

#kc_forall_tree ch397503psiAll (fun q => ch397503psi q = true) 24
  CertificateChecks.KernelU43Twin.ch397503psi

theorem L2dig {v : ℕ} (hv : v < 24) : Dig (L2 v) := (L2mem v hv).1

theorem L1dig {v : ℕ} (hv : v < 24) : Dig (L1 v) := (L1mem v hv).1

theorem psiOK_true : psiOK () = true := by
  unfold psiOK
  rw [slPin]
  simp only [List.all_map, Bool.and_eq_true, List.all_eq_true, List.mem_range, Function.comp_apply]
  refine ⟨fun v hv => ?_, fun a ha b hb => ?_⟩
  · obtain ⟨r1, -, c1, c2, -⟩ := psiRowK_spec (ch397503psiAll v hv)
    obtain ⟨s1, s2⟩ := psiShape v hv
    refine ⟨⟨⟨⟨?_, s1⟩, ?_⟩, ?_⟩, s2⟩
    · rw [psiV v hv]
      exact rawValid_dec r1
    · rw [psiV v hv, P2Eq]
      exact commK_spec (L2dig hv) (fxDig (by norm_num)) c1
    · rw [psiV v hv, Q2Eq]
      exact commK_spec (L2dig hv) (fxDig (by norm_num)) c2
  · obtain ⟨hm, hq⟩ := mtPin a ha b hb
    obtain ⟨-, -, -, -, hr⟩ := psiRowK_spec (ch397503psiAll a ha)
    rw [hq, psiV _ hm, psiV a ha, psiV b hb, mulRaw_dec (L2dig ha) (L2dig hb),
      eqZ_dec (L2dig hm) (mulK_dig (L2dig ha) (L2dig hb))]
    exact (hr b hb).1

theorem commOK_true : commOK () = true := by
  unfold commOK
  rw [h2Pin, slPin]
  simp only [List.all_map, Bool.and_eq_true, List.all_eq_true, List.mem_range, Function.comp_apply]
  intro b hb
  refine ⟨?_, fun a ha => ?_⟩
  · exact rawValid_dec (psiRowK_spec (ch397503psiAll b hb)).2.1
  · obtain ⟨-, -, -, -, hr⟩ := psiRowK_spec (ch397503psiAll a ha)
    rw [psiV a ha]
    exact commK_spec (L2dig ha) (L1dig hb) (hr b hb).2

theorem t0Shape : innerShape T0 = true := by decide +kernel

theorem t0NZ : isZ T0 = false := by decide +kernel

theorem t0Sq : isZK (mulK T0K T0K) = true := by decide +kernel

theorem t0Comm : ∀ k < 4, commK (KernelU43Pk.G k) T0K = true := by decide +kernel

theorem t0OK_true : t0OK () = true := by
  have hsz : u43Data.gens.size = 4 := rfl
  unfold t0OK
  rw [hsz, t0Shape, t0NZ]
  simp only [Bool.and_true, Bool.not_false, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨?_, ?_⟩, fun k hk => ?_⟩
  · rw [T0Eq]
    exact rawValid_dec T0V
  · rw [T0Eq, mulRaw_dec T0Dig T0Dig, isZ_dec (mulK_lt _ _)]
    exact t0Sq
  · rw [KernelU43Pk.gensEq k hk, T0Eq]
    exact commK_spec (dig_of (KernelU43Pk.gensV k hk)) T0Dig (t0Comm k hk)

theorem G0Eq : G0 = dec G0K := by decide +kernel

theorem qShape : innerShape P1 = true ∧ innerShape Q1 = true ∧ innerShape P2 = true ∧
    innerShape Q2 = true ∧ innerShape G0 = true := by decide +kernel

theorem qV : rawValidK (FX 37) = true ∧ rawValidK (FX 40) = true ∧ rawValidK (FX 45) = true ∧
    rawValidK (FX 48) = true := by decide +kernel

theorem G0V : rawValidK G0K = true ∧ rawValidK (conjTK G0K) = true ∧
    isZK (mulK G0K (conjTK G0K)) = true := by decide +kernel

theorem G0Dig : Dig G0K := dig_of G0V.1

@[expose] noncomputable def q8PairK (P Q : ℕ) : Bool :=
  Nat.beq (nrmK (mulK P P)) (nrmK T0K) && Nat.beq (nrmK (mulK Q Q)) (nrmK T0K) &&
    Nat.beq (nrmK (mulK Q P)) (nrmK (mulK (mulK T0K P) Q))

theorem q8PairC_dec {P Q : ℕ} (hP : Dig P) (hQ : Dig Q) : q8PairC (dec P) (dec Q) = q8PairK P Q := by
  unfold q8PairC q8PairK
  rw [T0Eq, mulRaw_dec hP hP, mulRaw_dec hQ hQ, mulRaw_dec hQ hP, mulRaw_dec T0Dig hP,
    mulRaw_dec (mulK_dig T0Dig hP) hQ, eqZ_dec (mulK_dig hP hP) T0Dig,
    eqZ_dec (mulK_dig hQ hQ) T0Dig, eqZ_dec (mulK_dig hQ hP) (mulK_dig (mulK_dig T0Dig hP) hQ)]

theorem q8Pairs : q8PairK (FX 37) (FX 40) = true ∧ q8PairK (FX 45) (FX 48) = true := by
  decide +kernel

theorem G0Comm : commK G0K T0K = true := by decide +kernel

theorem G0Conj : Nat.beq (nrmK (cbK G0K (FX 45))) (nrmK (EL 0 7)) = true ∧
    Nat.beq (nrmK (cbK G0K (FX 48))) (nrmK (EL 0 6)) = true := by decide +kernel

theorem qOK_true : qOK () = true := by
  obtain ⟨sP1, sQ1, sP2, sQ2, sG0⟩ := qShape
  obtain ⟨vP1, vQ1, vP2, vQ2⟩ := qV
  have d45 : Dig (FX 45) := dig_of vP2
  have d48 : Dig (FX 48) := dig_of vQ2
  unfold qOK
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, sP1⟩, ⟨?_, sQ1⟩, ⟨?_, sP2⟩, ?_, sQ2⟩, ?_⟩, ?_⟩, ?_⟩, sG0⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [P1Eq]
    exact rawValid_dec vP1
  · rw [Q1Eq]
    exact rawValid_dec vQ1
  · rw [P2Eq]
    exact rawValid_dec vP2
  · rw [Q2Eq]
    exact rawValid_dec vQ2
  · rw [P1Eq, Q1Eq, q8PairC_dec (dig_of vP1) (dig_of vQ1)]
    exact q8Pairs.1
  · rw [P2Eq, Q2Eq, q8PairC_dec d45 d48]
    exact q8Pairs.2
  · rw [G0Eq]
    exact invertC_dec G0V.1 G0V.2.1 G0V.2.2
  · rw [G0Eq, T0Eq]
    exact commK_spec G0Dig T0Dig G0Comm
  · obtain ⟨d, m⟩ := E1mem 7 (by norm_num)
    rw [G0Eq, P2Eq, conjBy_dec G0Dig d45]
    exact memL_dec (cbK_dig G0Dig d45) d m G0Conj.1
  · obtain ⟨d, m⟩ := E1mem 6 (by norm_num)
    rw [G0Eq, Q2Eq, conjBy_dec G0Dig d48]
    exact memL_dec (cbK_dig G0Dig d48) d m G0Conj.2

theorem candShape : innerShape (dec (FX 35)) = true := by decide +kernel

theorem candV : rawValidK (FX 35) = true ∧ rawValidK (conjTK (FX 35)) = true ∧
    isZK (mulK (FX 35) (conjTK (FX 35))) = true ∧ commK (FX 35) T0K = true := by decide +kernel

theorem candsOK_true : candsOK () = true := by
  obtain ⟨v1, v2, v3, v4⟩ := candV
  unfold candsOK
  rw [candsPin]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨⟨invertC_dec v1 v2 v3, candShape⟩, ?_⟩
  rw [T0Eq]
  exact commK_spec (dig_of v1) T0Dig v4

end CertificateChecks.KernelU43Twin

end
