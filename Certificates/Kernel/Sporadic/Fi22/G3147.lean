
module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
meta import CFSG.Monster.B.Fischer.PinnedChainData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22CGT CFSG.Monster.B.Fischer.fi22ChainGenHex

#kmisc_hexflat CertificateChecks.KernelSpor.Fi22CGT CFSG.Monster.B.Fischer.fi22ChainGenHex 3 3510 12 2

namespace CertificateChecks.KernelSpor.Fi22G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native

theorem gen_eq {k : Nat} (hk : k < 2) : fi22ChainGen k = unpack 3510 12 (Fi22CGT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound Fi22CGT.all k hk
  rw [← Fi22CGT.eq] at h
  exact h

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 3510 12 (mask 12) (3510 * 12) p

@[expose] noncomputable def a01 : Nat := pcomp 3510 12 (mask 12) (Fi22CGT.F 0) (Fi22CGT.F 1)

@[expose] noncomputable def pw (p e : Nat) : Nat := powK 3510 12 p e

@[expose] noncomputable def idP : Nat := pidn 3510 12

theorem cnId : cn idP = true := by quickRfl
theorem idOK : idK 3510 12 (mask 12) = true := by quickRfl
theorem cn0 : cn (Fi22CGT.F 0) = true := by quickRfl
theorem cn1 : cn (Fi22CGT.F 1) = true := by quickRfl
theorem p0 : Nat.beq (pw (Fi22CGT.F 0) 2) idP = true := by quickRfl
theorem n0 : Bool.not (Nat.beq (Fi22CGT.F 0) idP) = true := by quickRfl
theorem p1 : Nat.beq (pw (Fi22CGT.F 1) 13) idP = true := by quickRfl
theorem n1 : Bool.not (Nat.beq (Fi22CGT.F 1) idP) = true := by quickRfl
theorem p01 : Nat.beq (pw a01 11) idP = true := by quickRfl
theorem n01 : Bool.not (Nat.beq a01 idP) = true := by quickRfl

theorem powA_unpack {p : Nat} (hp : cn p = true) :
    ∀ e, powA 3510 (unpack 3510 12 p) e = unpack 3510 12 (pw p e)
  | 0 => by
    rw [powA, ← idK_sound idOK]
    rfl
  | e + 1 => by
    rw [powA, powA_unpack hp e]
    unfold pw
    rw [compA_unpack hp (canonK_powK cnId hp e)]
    rfl

theorem eqA_true {p q : Nat} (hp : cn p = true) (hq : cn q = true) (h : Nat.beq p q = true) :
    eqA 3510 (unpack 3510 12 p) (unpack 3510 12 q) = true := by
  rw [eqA_unpack hp hq]
  exact h

theorem eqA_false {p q : Nat} (hp : cn p = true) (hq : cn q = true)
    (h : Bool.not (Nat.beq p q) = true) :
    eqA 3510 (unpack 3510 12 p) (unpack 3510 12 q) = false := by
  rw [eqA_unpack hp hq]
  cases e : Nat.beq p q
  · rfl
  · rw [e] at h
    exact absurd h (by decide)

theorem orders :
    eqA 3510 (powA 3510 (fi22ChainGen 0) 2) (idA 3510) = true ∧
    eqA 3510 (fi22ChainGen 0) (idA 3510) = false ∧
    eqA 3510 (powA 3510 (fi22ChainGen 1) 13) (idA 3510) = true ∧
    eqA 3510 (fi22ChainGen 1) (idA 3510) = false ∧
    eqA 3510 (powA 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) 11) (idA 3510) = true ∧
    eqA 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) (idA 3510) = false := by
  have hc01 : cn a01 = true := canonK_pcomp cn0 cn1
  have h01 : compA 3510 (fi22ChainGen 0) (fi22ChainGen 1) = unpack 3510 12 a01 := by
    rw [gen_eq (by norm_num), gen_eq (by norm_num)]
    exact compA_unpack cn0 cn1
  rw [← idK_sound idOK, h01, gen_eq (k := 0) (by norm_num), gen_eq (k := 1) (by norm_num),
    powA_unpack cn0, powA_unpack cn1, powA_unpack hc01]
  exact ⟨eqA_true (canonK_powK cnId cn0 2) cnId p0, eqA_false cn0 cnId n0,
    eqA_true (canonK_powK cnId cn1 13) cnId p1, eqA_false cn1 cnId n1,
    eqA_true (canonK_powK cnId hc01 11) cnId p01, eqA_false hc01 cnId n01⟩

end CertificateChecks.KernelSpor.Fi22G

end
