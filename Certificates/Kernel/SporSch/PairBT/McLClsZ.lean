module

public import Certificates.Kernel.SporSch.PairBT.McLData
public import Certificates.Kernel.SporSch.PairBT.McLSylChk
public import Certificates.Kernel.SporSch.J4S.Gen
public import Certificates.Data.Kernel.SporSch.ClsZK
public meta import Certificates.Kernel.SporSch.PairBT.McLData
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLZC

open CFSG.KS.RawGen CertificateChecks.KernelSporSch.McLBT

meta def stM : Array (Array Nat) := Id.run do
  let Ai := inv 275 tAM
  let Bi := inv 275 tBM
  let mut bl : Array (Nat × Array Nat) := #[(pack 9 tAM, tAM)]
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (pack 9 tAM)
  let mut h := 0
  while h < bl.size do
    let x := bl[h]!.2
    for z in [comp 275 tAM (comp 275 x Ai), comp 275 tBM (comp 275 x Bi)] do
      let c := pack 9 z
      if !seen.contains c then
        seen := seen.insert c
        bl := bl.push (c, z)
    h := h + 1
  return (bl.qsort fun a b => a.1 < b.1).map (·.2)

meta def rows (s : String) : Array (Array Nat) :=
  ((s.splitOn "\n").filter (· ≠ "")).toArray.map fun l => ((l.splitOn " ").map String.toNat!).toArray

meta def treeM : Array (Array Nat) := rows (include_str "McLClsTree.txt")

meta def paM : Array (Array Nat) := treeM.map fun r => #[r[0]!]

meta def lbM : Array (Array Nat) := treeM.map fun r => #[r[1]!]

meta def dpM : Array (Array Nat) := treeM.map fun r => #[r[2]!]

meta def iaM : Array (Array Nat) := treeM.map fun r => #[r[3]!]

meta def ibM : Array (Array Nat) := treeM.map fun r => #[r[4]!]

meta def otM : Array (Array Nat) := rows (include_str "McLZOrb.txt")

meta def rpM : Array (Array Nat) :=
  ((Array.range otM.size).filter fun k => (otM[k]!)[2]! == 0).map fun k => #[k]

end CertificateChecks.KernelSporSch.McLZC

#kss_tree CertificateChecks.KernelSporSch.McLZC.ST CertificateChecks.KernelSporSch.McLZC.stM 9
#kss_tree CertificateChecks.KernelSporSch.McLZC.PA CertificateChecks.KernelSporSch.McLZC.paM 16
#kss_tree CertificateChecks.KernelSporSch.McLZC.LB CertificateChecks.KernelSporSch.McLZC.lbM 16
#kss_tree CertificateChecks.KernelSporSch.McLZC.DP CertificateChecks.KernelSporSch.McLZC.dpM 16
#kss_tree CertificateChecks.KernelSporSch.McLZC.IA CertificateChecks.KernelSporSch.McLZC.iaM 16
#kss_tree CertificateChecks.KernelSporSch.McLZC.IB CertificateChecks.KernelSporSch.McLZC.ibM 16
#kss_tree CertificateChecks.KernelSporSch.McLZC.OT CertificateChecks.KernelSporSch.McLZC.otM 16
#kss_tree CertificateChecks.KernelSporSch.McLZC.RP CertificateChecks.KernelSporSch.McLZC.rpM 16

namespace CertificateChecks.KernelSporSch.McLZC

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MBT CFSG.KS.SporSch.MOC

@[expose] noncomputable def clsD : ClsD := ⟨PMcL.S 0, 22275, 19079, ST, IA, IB, PA, LB, DP⟩

theorem hd : clsHdK 275 9 (mask 9) 2 30000 clsD = true := by quickRfl

@[expose] noncomputable def srt : Nat → Bool := clsSrtK (275 * 9) clsD

@[expose] noncomputable def tree : Nat → Bool := fun j =>
  Bool.rec (motive := fun _ => Bool) true (zRepTreeK 275 9 (mask 9) (PMcL.S 0) (PMcL.SI 0) (PMcL.S 1)
    (PMcL.SI 1) McLSylChk.Z McLSylChk.Zi RP OT clsD j) (Nat.blt j 2025)

end CertificateChecks.KernelSporSch.McLZC

#kss_slices CertificateChecks.KernelSporSch.McLZCS CertificateChecks.KernelSporSch.McLZC.srt 256 88
#kss_slices CertificateChecks.KernelSporSch.McLZCT CertificateChecks.KernelSporSch.McLZC.tree 256 8

end
