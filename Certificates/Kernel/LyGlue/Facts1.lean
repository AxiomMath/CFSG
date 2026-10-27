module

public import Certificates.Kernel.LyGlue.Data
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelY
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelTr
import CFSG.Certificates.Kernel.Child3Reps

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native

theorem natArr_get {T : Table} {v : Nat} (hv : v < T.size) : (natArr T)[v]! = (T[v]!).toNat := by
  rw [getElem!_pos _ v (by simpa [natArr] using hv), getElem!_pos T v hv]
  simp [natArr]

theorem pg_of_rep {n w F : Nat} {T : Table} {g : Equiv.Perm (Fin n)} (hsz : T.size = n)
    (hT : natArr T = unpack n w F) (hr : Rep n T g) {v : Nat} (hv : v < n) :
    pg w (mask w) F v = (g ⟨v, hv⟩ : Nat) := by
  have h1 := hr v hv
  rw [idx_of_lt _ hv] at h1
  rw [← CFSG.KC.Child3.unpack_get' hv, ← hT, natArr_get (by omega)]
  exact h1

theorem ug_pg (hY : Ly1080.YOK) {k : Nat} (hk : k < 4) {v : Nat} (hv : v < 1080) :
    pg 11 (mask 11) (UH.F k) v = (Ly1080.ug k ⟨v, hv⟩ : Nat) := by
  have hT : Ly1080.uTabs[k]! = CFSG.Sporadic.SmallOddCore.Native.hexT 3 1080 (1080 * k)
      (String.ofList UH.chars) := by
    rw [← UH.eq]
    unfold Ly1080.uTabs
    rw [getElem!_pos _ k (by simp; exact hk), Array.getElem_ofFn]
  refine pg_of_rep (T := Ly1080.uTabs[k]!) ?_ ?_ (Ly1080.rep_u (Ly1080.yCheck_tables hY) hk) hv
  · rw [hT]
    simp [CFSG.Sporadic.SmallOddCore.Native.hexT]
  · rw [hT]
    exact CFSG.KC.Misc.HexFlat.hexT_sound UH.all (by norm_num) k hk

theorem gg_pg (hT : Ly243.trCheck = true) {k : Nat} (hk : k < 5) {v : Nat} (hv : v < 243) :
    pg 8 (mask 8) (GH.F k) v = (Ly243.gg k ⟨v, hv⟩ : Nat) := by
  have e : Ly243.genTabs[k]! = CFSG.Sporadic.SmallOddCore.Native.hexT 2 243 (243 * k)
      (String.ofList GH.chars) := by
    rw [← GH.eq]
    unfold Ly243.genTabs
    rw [getElem!_pos _ k (by simp; exact hk), Array.getElem_ofFn]
  refine pg_of_rep (T := Ly243.genTabs[k]!) ?_ ?_ (Ly243.rep_gg hT hk) hv
  · rw [e]
    simp [CFSG.Sporadic.SmallOddCore.Native.hexT]
  · rw [e]
    exact CFSG.KC.Misc.HexFlat.hexT_sound GH.all (by norm_num) k hk

theorem lineG_pg (hT : Ly243.trCheck = true) {k : Nat} (hk : k < 3) {v : Nat} (hv : v < 243) :
    pg 8 (mask 8) (LH.F k) v = (Ly243.lineG k ⟨v, hv⟩ : Nat) := by
  have e : Ly243.lineTabs[k]! = CFSG.Sporadic.SmallOddCore.Native.hexT 2 243 (243 * k)
      (String.ofList LH.chars) := by
    rw [← LH.eq]
    unfold Ly243.lineTabs
    rw [getElem!_pos _ k (by simp; exact hk), Array.getElem_ofFn]
  refine pg_of_rep (T := Ly243.lineTabs[k]!) ?_ ?_ (Ly243.rep_lineG hT hk) hv
  · rw [e]
    simp [CFSG.Sporadic.SmallOddCore.Native.hexT]
  · rw [e]
    exact CFSG.KC.Misc.HexFlat.hexT_sound LH.all (by norm_num) k hk

end CertificateChecks.KernelLy

end
