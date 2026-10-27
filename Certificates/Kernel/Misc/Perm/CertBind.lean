module

public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Monster.B.Fischer.ArrCert

public section

namespace CertificateChecks.KernelMisc.CertBind

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.HexFlat

@[expose] def Bound (n w : ℕ) (c : CFSG.Monster.B.Fischer.ArrCert) (N G : ℕ)
    (FP FE FR FL : ℕ → ℕ) : Prop :=
  c.pts.size = N ∧ (∀ i < N, c.pts[i]! = unpack n w (FP i)) ∧
    (∀ i < N, (c.edges[i]!).size = G ∧ ∀ k < G, (c.edges[i]!)[k]! = pg 12 (mask 12) (FE i) k) ∧
    (∀ i < N, c.par[i]! = pg 12 (mask 12) (FR 0) i ∧ c.lab[i]! = pg 12 (mask 12) (FL 0) i)

theorem cert_facts {n w N G : ℕ} {PH EH RH LH : String} {csP csE csR csL : List Char}
    {FP FE FR FL : ℕ → ℕ} (hPs : PH = String.ofList csP) (hPa : hexFlat csP 3 n w N FP = true)
    (hEs : EH = String.ofList csE) (hEa : hexFlat csE 3 G 12 N FE = true)
    (hRs : RH = String.ofList csR) (hRa : hexFlat csR 3 N 12 1 FR = true)
    (hLs : LH = String.ofList csL) (hLa : hexFlat csL 3 N 12 1 FL = true) :
    Bound n w ⟨Array.ofFn fun i : Fin N => CFSG.Monster.B.Fischer.hexTable3 n (n * i.val) PH,
        Array.ofFn fun i : Fin N => CFSG.Monster.B.Fischer.hexTable3 G (G * i.val) EH,
        CFSG.Monster.B.Fischer.hexTable3 N 0 RH, CFSG.Monster.B.Fischer.hexTable3 N 0 LH⟩
      N G FP FE FR FL := by
  have hr : CFSG.Monster.B.Fischer.hexTable3 N 0 RH = unpack N 12 (FR 0) := by
    have h := hexTable3_sound hRa 0 (by norm_num)
    rwa [Nat.mul_zero, ← hRs] at h
  have hl : CFSG.Monster.B.Fischer.hexTable3 N 0 LH = unpack N 12 (FL 0) := by
    have h := hexTable3_sound hLa 0 (by norm_num)
    rwa [Nat.mul_zero, ← hLs] at h
  refine ⟨by simp, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · change
      (Array.ofFn fun i : Fin N => CFSG.Monster.B.Fischer.hexTable3 n (n * i.val) PH)[i]! = _
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, hPs]
    exact hexTable3_sound hPa i hi
  · have he : (Array.ofFn fun i : Fin N => CFSG.Monster.B.Fischer.hexTable3 G (G * i.val) EH)[i]! =
        unpack G 12 (FE i) := by
      rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, hEs]
      exact hexTable3_sound hEa i hi
    change (Array.ofFn fun i : Fin N => CFSG.Monster.B.Fischer.hexTable3 G (G * i.val) EH)[i]!.size
      = G ∧ _
    rw [he]
    exact ⟨by simp [unpack], fun k hk => CFSG.KC.Misc.PairCount.unpack_get hk⟩
  · change (CFSG.Monster.B.Fischer.hexTable3 N 0 RH)[i]! = _ ∧
      (CFSG.Monster.B.Fischer.hexTable3 N 0 LH)[i]! = _
    rw [hr, hl]
    exact ⟨CFSG.KC.Misc.PairCount.unpack_get hi, CFSG.KC.Misc.PairCount.unpack_get hi⟩

end CertificateChecks.KernelMisc.CertBind

end
