module

public import Certificates.Kernel.HS100.FiveData
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.RankThree.Native.HSMcLFiveCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Misc.HexFlat
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native

theorem hw : szOK 100 7 = true := by quickRfl

theorem fiveArr_eq (j : ℕ) (hj : j < 82) : hs100FiveArr j = unpack 100 7 (FV.F j) := by
  rw [hs100FiveArr, FV.eq]
  exact hexTable3_sound FV.all j hj

theorem ppF {j : ℕ} (hj : j < 82) : PP 100 7 (FV.F j) :=
  PP_of_permOK hw (allN_spec permF j hj)

theorem fiveLine_eq {j : ℕ} (hj : j < 31) : hs100FiveLines[j]! = unpack 100 7 (FV.F (j + 2)) := by
  unfold hs100FiveLines
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact fiveArr_eq (j + 2) (by omega)

theorem keys_lt : ∀ p ∈ hs100FiveKeys, p < 100 := by decide

theorem hsKeys : hs100FiveKeys = [0, 1, 3, 2, 4, 5] := by decide

theorem c0_gens : hs100FiveC0Gens.size = C0.ng ∧
    ∀ k < C0.ng, hs100FiveC0Gens[k]! = unpack 100 7 (C0.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk3 : k < 3 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec gensF.1 k hk3)]
  interval_cases k <;> exact fiveArr_eq _ (by norm_num)

theorem c0_permG : ∀ k < C0.ng, permOK 100 7 (mask 7) (100 * 7) (C0.G k)
    (pinvS 100 7 (mask 7) (C0.G k)) = true := by
  intro k hk
  have hk3 : k < 3 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec gensF.1 k hk3)]
  exact allN_spec permF _ (by omega)

theorem c0_pts : hs100FiveC0Cert.pts = Array.ofFn (n := C0.N) fun i => unpack 100 7 (C0.T i.val) := by
  unfold hs100FiveC0Cert
  rw [hsKeys]
  exact enumBfs_pts_base c0_gens.1 c0_gens.2 C0.ok (by decide) C0.keys (by decide)

theorem c0_enumOK : enumOK 100 hs100FiveC0Gens hs100FiveKeys hs100FiveC0Cert = true := by
  unfold hs100FiveC0Cert
  rw [hsKeys]
  exact enumOK_of_bfsK_base c0_gens.1 c0_gens.2 c0_permG C0.ok (by decide) C0.keys (by decide)

theorem c0_pp : ∀ i < C0.N, PP 100 7 (C0.T i) := PP_pts C0.ok c0_permG

theorem c2_gens : hs100FiveC2Gens.size = C2.ng ∧
    ∀ k < C2.ng, hs100FiveC2Gens[k]! = unpack 100 7 (C2.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk4 : k < 4 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec gensF.2.1 k hk4)]
  interval_cases k <;> exact fiveArr_eq _ (by norm_num)

theorem c2_permG : ∀ k < C2.ng, permOK 100 7 (mask 7) (100 * 7) (C2.G k)
    (pinvS 100 7 (mask 7) (C2.G k)) = true := by
  intro k hk
  have hk4 : k < 4 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec gensF.2.1 k hk4)]
  exact allN_spec permF _ (by omega)

theorem c2_pts : hs100FiveC2Cert.pts = Array.ofFn (n := C2.N) fun i => unpack 100 7 (C2.T i.val) := by
  unfold hs100FiveC2Cert
  rw [hsKeys]
  exact enumBfs_pts_base c2_gens.1 c2_gens.2 C2.ok (by decide) C2.keys (by decide)

theorem c2_enumOK : enumOK 100 hs100FiveC2Gens hs100FiveKeys hs100FiveC2Cert = true := by
  unfold hs100FiveC2Cert
  rw [hsKeys]
  exact enumOK_of_bfsK_base c2_gens.1 c2_gens.2 c2_permG C2.ok (by decide) C2.keys (by decide)

theorem c2_pp : ∀ i < C2.N, PP 100 7 (C2.T i) := PP_pts C2.ok c2_permG

theorem c23_gens : hs100FiveC23Gens.size = C23.ng ∧
    ∀ k < C23.ng, hs100FiveC23Gens[k]! = unpack 100 7 (C23.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk4 : k < 4 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec gensF.2.2 k hk4)]
  interval_cases k <;> exact fiveArr_eq _ (by norm_num)

theorem c23_permG : ∀ k < C23.ng, permOK 100 7 (mask 7) (100 * 7) (C23.G k)
    (pinvS 100 7 (mask 7) (C23.G k)) = true := by
  intro k hk
  have hk4 : k < 4 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec gensF.2.2 k hk4)]
  exact allN_spec permF _ (by omega)

theorem c23_pts : hs100FiveC23Cert.pts =
    Array.ofFn (n := C23.N) fun i => unpack 100 7 (C23.T i.val) := by
  unfold hs100FiveC23Cert
  rw [hsKeys]
  exact enumBfs_pts_base c23_gens.1 c23_gens.2 C23.ok (by decide) C23.keys (by decide)

theorem c23_enumOK : enumOK 100 hs100FiveC23Gens hs100FiveKeys hs100FiveC23Cert = true := by
  unfold hs100FiveC23Cert
  rw [hsKeys]
  exact enumOK_of_bfsK_base c23_gens.1 c23_gens.2 c23_permG C23.ok (by decide) C23.keys
    (by decide)

theorem c23_pp : ∀ i < C23.N, PP 100 7 (C23.T i) := PP_pts C23.ok c23_permG

end CertificateChecks.KernelHS100

end
