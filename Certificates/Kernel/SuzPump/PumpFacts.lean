module

public import Certificates.Kernel.SuzPump.PumpPairK
public import Certificates.Kernel.SuzPump.PumpY
public import Certificates.Kernel.SuzPump.PairFacts
public import Certificates.Kernel.Sporadic.OddCore.S8147E
import CFSG.Certificates.Kernel.LocalQTCovTPrim
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzPump

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor
open CFSG.HardMathSupport.Solomon.Coordinator.SuzPump CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2 (allLt_iff)

theorem hPG : ∀ k < 2, pumpGs[k]! = unpack 1782 11 (SPP.G k) := by
  intro k hk
  interval_cases k
  · change rebuild (levels ()) g1β = _
    rw [rebuild_eq prb1.1, Nat.eq_of_beq_eq_true prb1.2]
  · change rebuild (levels ()) g2β = _
    rw [rebuild_eq prb2.1, Nat.eq_of_beq_eq_true prb2.2]

theorem pump_pair : pairCheck () = true := by
  obtain ⟨he1, he2, -, -⟩ := S8147.enumF (gs := pumpGs) (L := 60) (K := 126) (fuel := 8000)
    rfl hPG (by norm_num) (by norm_num) hPP dPP kPP pPP PPK.all (by norm_num)
  have hgk : ∀ k < 2, (okP (levels ()) pumpGs[k]! &&
      commA 1782 pumpGs[k]! (rebuild (levels ()) xAβ) &&
      eqA 1782 (powArr 1782 pumpGs[k]! 5) (idA 1782) && !(eqA 1782 pumpGs[k]! (idA 1782))) =
        true := by
    intro k hk
    obtain ⟨hp, hc, h5, h1⟩ := pgens k hk
    rw [hPG k hk, hX]
    unfold okP inP commA CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.levels
    rw [validA_of hp, siftA_of Suz2306.binds Suz2306.perm SuzC.hl (psiftG k hk),
      comp_unpack' hw hp pX, comp_unpack' hw pX hp,
      eqA_unpack' hw (permB_pcomp hw hp pX) (permB_pcomp hw pX hp), powEq_id hw hp, eqA_id hw hp]
    change (true && true && Nat.beq (cm 1782 11 (SPP.G k) XA) (cm 1782 11 XA (SPP.G k)) &&
      Nat.beq (pw 1782 11 (SPP.G k) 5) (pidn 1782 11) && !Nat.beq (SPP.G k) (pidn 1782 11)) = true
    rw [hc, h5, h1]
    rfl
  unfold pairCheck pairCheckG
  change (pumpGs.size == 2 && allLt 2 (fun i => okP (levels ()) pumpGs[i]! &&
      commA 1782 pumpGs[i]! (rebuild (levels ()) xAβ) &&
      eqA 1782 (powArr 1782 pumpGs[i]! 5) (idA 1782) && !(eqA 1782 pumpGs[i]! (idA 1782))) &&
    (enumOK 1782 pumpGs suzFiveKeys (enumBfs 1782 pumpGs suzFiveKeys 8000) &&
      decide (1080 < (enumBfs 1782 pumpGs suzFiveKeys 8000).pts.size))) = true
  rw [he1, he2, (allLt_iff).2 hgk]
  rfl

theorem okP_unpack {X : Nat} (hs : Nat.beq (Nat.shiftRight X (1782 * 11)) 0 = true ∧
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) X t) 1782) = true ∧
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 X = true)
    (hp : permB 1782 11 X = true) : okP (levels ()) (unpack 1782 11 X) = true := by
  unfold okP inP CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.levels
  rw [validA_of hp, siftA_of Suz2306.binds Suz2306.perm SuzC.hl hs]
  rfl

theorem commA_unp {p q : Nat} (hp : permB 1782 11 p = true) (hq : permB 1782 11 q = true) :
    commA 1782 (unpack 1782 11 p) (unpack 1782 11 q) =
      Nat.beq (cm 1782 11 p q) (cm 1782 11 q p) := by
  unfold commA
  rw [comp_unpack' hw hp hq, comp_unpack' hw hq hp,
    eqA_unpack' hw (permB_pcomp hw hp hq) (permB_pcomp hw hq hp)]
  rfl

theorem conjA_unp {g a : Nat} (hg : permB 1782 11 g = true) (ha : permB 1782 11 a = true)
    (hgi : permOK 1782 11 (mask 11) (1782 * 11) g (pinvS 1782 11 (mask 11) g) = true) :
    conjA 1782 (unpack 1782 11 g) (unpack 1782 11 a) =
      unpack 1782 11 (cm 1782 11 g (cm 1782 11 a (pinvS 1782 11 (mask 11) g))) := by
  unfold conjA
  rw [CFSG.KC.LQT.Cov.T.invCand_unpack hgi, comp_unpack' hw ha (permB_pinvS hw hg),
    comp_unpack' hw hg (permB_pcomp hw ha (permB_pinvS hw hg))]
  rfl

theorem hYG : ∀ k < 2, yGs[k]! = unpack 1782 11 (YE.G k) := by
  intro k hk
  interval_cases k
  · change rebuild (levels ()) uβ = _
    rw [rebuild_eq yrb1.1, Nat.eq_of_beq_eq_true yrb1.2]
  · change rebuild (levels ()) vβ = _
    rw [rebuild_eq yrb2.1, Nat.eq_of_beq_eq_true yrb2.2]

theorem hYng : YE.ng = 2 := Nat.eq_of_beq_eq_true yn0.2

theorem hYN : YE.N = 360 := Nat.eq_of_beq_eq_true yn0.1

theorem mem_of_any {X : Nat} (h : CFSG.KC.LQT.P.anyN YE.N (fun i => Nat.beq (YE.T i) X) = true)
    {c : CFSG.Monster.B.Fischer.ArrCert} (hs : c.pts.size = YE.N)
    (hT : ∀ i < YE.N, c.pts[i]! = unpack 1782 11 (YE.T i)) :
    c.pts.toList.any (eqA 1782 (unpack 1782 11 X)) = true := by
  rw [anyNP_eq, List.any_eq_true] at h
  obtain ⟨i, hi, hX⟩ := h
  rw [List.mem_range] at hi
  rw [List.any_eq_true]
  refine ⟨c.pts[i]'(by rw [hs]; exact hi), Array.getElem_mem_toList _, ?_⟩
  rw [← getElem!_pos c.pts i (by rw [hs]; exact hi), hT i hi, Nat.eq_of_beq_eq_true hX]
  exact CFSG.KS.Raw.eqA_self _

theorem pump_y : yCheck () = true := by
  have hbind : BindA 1782 11 yGs YE.ng YE.G := by
    rw [hYng]
    exact ⟨rfl, hYG⟩
  obtain ⟨he1, he2, he3⟩ := enum_of (fuel := 400) hbind
    (fun k hk => (ysift (YE.G k) (by
      rw [hYng] at hk
      interval_cases k <;> simp)).2.2.1)
    YE.ok (by rw [hkeys]; decide) YE.keys (by rw [hYN]; omega)
  rw [hkeys] at he1 he2 he3
  have sX := fun X (hX : X ∈ [YE.G 0, YE.G 1, YY, AA, BB, GG]) => ysift X hX
  have pY := (sX YY (by simp)).2.2.1
  have pA := (sX AA (by simp)).2.2.1
  have pB := (sX BB (by simp)).2.2.1
  have pG := (sX GG (by simp)).2.2.1
  obtain ⟨mA, mB, a3, a1, b3, b1, cab, bna, bna2, gperm, cga, cgb⟩ := yab
  have rY : rebuild (levels ()) yTuple = unpack 1782 11 YY := rebuild_eq yrb.1
  have rA : rebuild (levels ()) aβ = unpack 1782 11 AA := rebuild_eq yrb.2.1
  have rB : rebuild (levels ()) bβ = unpack 1782 11 BB := rebuild_eq yrb.2.2.1
  have rG : rebuild (levels ()) gβ = unpack 1782 11 GG := rebuild_eq yrb.2.2.2
  have hgk : ∀ k < 2, (okP (levels ()) yGs[k]! &&
      commA 1782 yGs[k]! (rebuild (levels ()) yTuple) &&
      eqA 1782 (powArr 1782 yGs[k]! 10) (idA 1782)) = true := by
    intro k hk
    have hk' : YE.G k ∈ [YE.G 0, YE.G 1, YY, AA, BB, GG] := by
      interval_cases k <;> simp
    obtain ⟨s1, s2, hp, s3⟩ := sX _ hk'
    obtain ⟨hc, h10⟩ := ygens k hk
    rw [hYG k hk, rY, okP_unpack ⟨s1, s2, s3⟩ hp, commA_unp hp pY,
      powEq_id hw hp]
    change (true && Nat.beq (cm 1782 11 (YE.G k) YY) (cm 1782 11 YY (YE.G k)) &&
      Nat.beq (pw 1782 11 (YE.G k) 10) (pidn 1782 11)) = true
    rw [hc, h10]
    rfl
  have oA : okP (levels ()) (unpack 1782 11 AA) = true := by
    obtain ⟨s1, s2, hp, s3⟩ := sX AA (by simp)
    exact okP_unpack ⟨s1, s2, s3⟩ hp
  have oB : okP (levels ()) (unpack 1782 11 BB) = true := by
    obtain ⟨s1, s2, hp, s3⟩ := sX BB (by simp)
    exact okP_unpack ⟨s1, s2, s3⟩ hp
  have oG : okP (levels ()) (unpack 1782 11 GG) = true := by
    obtain ⟨s1, s2, hp, s3⟩ := sX GG (by simp)
    exact okP_unpack ⟨s1, s2, s3⟩ hp
  unfold yCheck yCheckG yArr
  change (yGs.size == 2 && allLt 2 (fun i => okP (levels ()) yGs[i]! &&
      commA 1782 yGs[i]! (rebuild (levels ()) yTuple) &&
      eqA 1782 (powArr 1782 yGs[i]! 10) (idA 1782)) &&
    (enumOK 1782 yGs suzFiveKeys (enumBfs 1782 yGs suzFiveKeys 400) &&
      (enumBfs 1782 yGs suzFiveKeys 400).pts.size == 360 &&
      okP (levels ()) (rebuild (levels ()) aβ) && okP (levels ()) (rebuild (levels ()) bβ) &&
      okP (levels ()) (rebuild (levels ()) gβ) &&
      (enumBfs 1782 yGs suzFiveKeys 400).pts.toList.any (eqA 1782 (rebuild (levels ()) aβ)) &&
      (enumBfs 1782 yGs suzFiveKeys 400).pts.toList.any (eqA 1782 (rebuild (levels ()) bβ)) &&
      eqA 1782 (powArr 1782 (rebuild (levels ()) aβ) 3) (idA 1782) &&
      !(eqA 1782 (rebuild (levels ()) aβ) (idA 1782)) &&
      eqA 1782 (powArr 1782 (rebuild (levels ()) bβ) 3) (idA 1782) &&
      !(eqA 1782 (rebuild (levels ()) bβ) (idA 1782)) &&
      commA 1782 (rebuild (levels ()) aβ) (rebuild (levels ()) bβ) &&
      !(eqA 1782 (rebuild (levels ()) bβ) (rebuild (levels ()) aβ)) &&
      !(eqA 1782 (rebuild (levels ()) bβ) (powArr 1782 (rebuild (levels ()) aβ) 2)) &&
      eqA 1782 (conjA 1782 (rebuild (levels ()) gβ) (rebuild (levels ()) aβ))
        (rebuild (levels ()) aβ) &&
      eqA 1782 (conjA 1782 (rebuild (levels ()) gβ) (rebuild (levels ()) bβ))
        (powArr 1782 (rebuild (levels ()) bβ) 2))) = true
  rw [rA, rB, rG]
  change (yGs.size == 2 && allLt 2 _ && (_ && _ && okP (levels ()) (unpack 1782 11 AA) &&
    okP (levels ()) (unpack 1782 11 BB) && okP (levels ()) (unpack 1782 11 GG) && _ && _ && _ && _ &&
    _ && _ && _ && _ && _ && _ && _)) = true
  rw [he1, he2, (allLt_iff).2 hgk, oA, oB, oG, mem_of_any mA he2 he3, mem_of_any mB he2 he3,
    powEq_id hw pA, powEq_id hw pB, eqA_id hw pA, eqA_id hw pB, commA_unp pA pB,
    eqA_unpack' hw pB pA, pow_unpack' hw pA, eqA_unpack' hw pB (permB_ppow hw pA 2),
    conjA_unp pG pA gperm, conjA_unp pG pB gperm, pow_unpack' hw pB]
  have e1 : eqA 1782 (unpack 1782 11 (cm 1782 11 GG (cm 1782 11 AA (pinvS 1782 11 (mask 11) GG))))
      (unpack 1782 11 AA) = Nat.beq (cm 1782 11 GG (cm 1782 11 AA (pinvS 1782 11 (mask 11) GG))) AA :=
    eqA_unpack' hw (permB_pcomp hw pG (permB_pcomp hw pA (permB_pinvS hw pG))) pA
  have e2 : eqA 1782 (unpack 1782 11 (cm 1782 11 GG (cm 1782 11 BB (pinvS 1782 11 (mask 11) GG))))
      (unpack 1782 11 (ppow 1782 11 (mask 11) (pidn 1782 11) BB 2)) =
      Nat.beq (cm 1782 11 GG (cm 1782 11 BB (pinvS 1782 11 (mask 11) GG))) (pw 1782 11 BB 2) :=
    eqA_unpack' hw (permB_pcomp hw pG (permB_pcomp hw pB (permB_pinvS hw pG))) (permB_ppow hw pB 2)
  rw [e1, e2]
  change (true && true && (true && true && true && true && true && true && true &&
    Nat.beq (pw 1782 11 AA 3) (pidn 1782 11) && !Nat.beq AA (pidn 1782 11) &&
    Nat.beq (pw 1782 11 BB 3) (pidn 1782 11) && !Nat.beq BB (pidn 1782 11) &&
    Nat.beq (cm 1782 11 AA BB) (cm 1782 11 BB AA) && !Nat.beq BB AA &&
    !Nat.beq BB (pw 1782 11 AA 2) &&
    Nat.beq (cm 1782 11 GG (cm 1782 11 AA (pinvS 1782 11 (mask 11) GG))) AA &&
    Nat.beq (cm 1782 11 GG (cm 1782 11 BB (pinvS 1782 11 (mask 11) GG))) (pw 1782 11 BB 2))) = true
  rw [a3, a1, b3, b1, cab, bna, bna2, cga, cgb]
  rfl

end CertificateChecks.KernelSuzPump

end
