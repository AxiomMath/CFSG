module

public import Certificates.Kernel.Item434.McLFive
public import Certificates.Kernel.Census.McLN
public import CFSG.Certificates.Kernel.Item434.PkSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Misc.ArrBind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelItem434

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Item434 CFSG.KC.Misc.HexFlat
open CFSG.Monster.B.Co2.Native CFSG.AGLEmbedding.KFactProofs.OrbitsCube CFSG.RankThree.Native

theorem pF5 {k : ℕ} (hk : k < 2) (hp : permB 275 9 (F5.F k) = true) :
    Pk 275 9 (mcl275FiveArr k) (F5.F k) := by
  refine ⟨?_, hp⟩
  unfold mcl275FiveArr
  rw [F5.eq]
  exact hexTable3_sound F5.all k hk

theorem five_ok : mclFiveNormCheck = true := by
  have px := pF5 (k := 0) (by norm_num) kFp.1
  have py := pF5 (k := 1) (by norm_num) kFp.2.1
  have ph : Pk 275 9 mclFiveNormArr (NH 0) := ⟨arrBind_sound (by quickRfl), kFp.2.2⟩
  have hs := kFs
  unfold siftM at hs
  simp only [Bool.and_eq_true] at hs
  have pc := pk_commutatorA kW px py
  unfold mclFiveNormCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨isInvA_pk px, isInvA_pk py⟩, isInvA_pk ph⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact siftK_soundR KernelCensus.McLK.binds KernelCensus.McLK.hperm KernelCensus.McLC.hl ph.1
      (Nat.eq_of_beq_eq_true hs.1.1) hs.1.2 hs.2
  · rw [eqA_pk kW pc (pk_id kW)]
    have e : Nat.beq fiveC idM = false := kFr.1
    unfold fiveC idM at e
    rw [e]
    rfl
  · unfold mclFiveWord
    rw [eqA_pk kW (pk_conjA kW ph px) (pk_comp kW (pk_comp kW (pk_powArr kW px 1)
      (pk_powArr kW py 2)) (pk_powArr kW pc 0))]
    exact kFr.2.1
  · unfold mclFiveWord
    rw [eqA_pk kW (pk_conjA kW ph py) (pk_comp kW (pk_comp kW (pk_powArr kW px 1)
      (pk_powArr kW py 4)) (pk_powArr kW pc 0))]
    exact kFr.2.2

end CertificateChecks.KernelItem434

end
