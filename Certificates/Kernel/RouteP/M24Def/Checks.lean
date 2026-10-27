module

public import Certificates.Kernel.RouteP.M24Def.Data
public import Certificates.Data.Kernel.RouteP.M24Def
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelM24Def

open CFSG.KC.M24Def Certificates.RouteP.M24Defect

set_option maxRecDepth 400000

theorem ch450210let : lettersTabOK LI LD LM = true := by quickRfl

theorem ch450210letters : lettersOK = true := by quickRfl

@[expose] noncomputable def ch450210tree (b : Nat) : Bool :=
  allLt 64 fun k => treeQ TW PA GQ FP LD LI (Nat.add (Nat.mul 64 b) k)

#kc_each ch450210tree 0 9

theorem ch450210relw : (((List.range 7).map fun i => decR (RW i)) == relWords) = true := by
  quickRfl

theorem ch450210rel : allLt 7 (fun i => relQ LI (RW i)) = true := by quickRfl

theorem ch450210ent : (csOf CB).all entriesOK = true := by quickRfl

theorem ch450210fs : allLt 67 (fun r => fsQ FP (CB r) (FS r)) = true := by quickRfl

theorem ch450210lam : allLt 7 (fun i => Nat.beq (lamOf LM (RW i)) (LA i)) = true := by quickRfl

theorem ch450210sd : allLt 77 (fun κ => Nat.blt (SD κ) 4194304) = true := by quickRfl

theorem ch450210bez :allLt 77 (fun κ => allLt 7 (bezQ LA FS SD TD κ)) = true := by quickRfl

@[expose] noncomputable def ch450210c (r : Nat) : Bool := comboK LD LI GQ FP RW (CB r)

#kc_each ch450210c 0 64

end CertificateChecks.KernelM24Def

end
