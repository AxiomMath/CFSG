module

public import Certificates.Data.Kernel.U43Mod.Defs
public import Certificates.Kernel.U43Mod.Data
public import Certificates.Kernel.Multipliers.U43BChain
public import Certificates.Data.U43ModelWords
public import CFSG.Quasithin.H13.GoldschmidtU43ModInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Mod

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KS CFSG.KS.Raw CFSG.KGroups.U43 CFSG.Quasithin.H13.U43
open CertificateChecks.KernelU43B

@[expose] def bs : List Nat := [0, 1, 9]

@[expose] noncomputable def GA (i q : Nat) : Nat := pg 10 (mask 10) (C.S i) q

@[expose] noncomputable def GAi (i q : Nat) : Nat := pg 10 (mask 10) (C.SI i) q

@[expose] def gW : List Word := [wordA, wordS, wordU, wordV, wordPhi]

@[expose] def sW : List Word := [sylWord0, sylWord1, sylWord2]

@[expose] noncomputable def GM (i q : Nat) : Nat := wG GA GAi gW i q

@[expose] noncomputable def GMi (i q : Nat) : Nat := wGi GA GAi gW i q

@[expose] noncomputable def GS (j q : Nat) : Nat := pg 10 (mask 10) (ST j) q

@[expose] noncomputable def inPU (p : Nat) : Bool :=
  siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0 p

@[expose] def sig2W : Word := [(2, false), (1, true), (2, true)]

theorem kRel5 : relsB bs GM GMi rels5Codes = true := by quickRfl

theorem kRel4 : relsB bs GM GMi rels4Codes = true := by quickRfl

theorem kComm : allN 4 (fun i => baseEq bs (fun q => GM i (GA 0 q)) (fun q => GA 0 (GM i q))) =
    true := by
  quickRfl

theorem kAB : (baseEq bs (wv GM GMi [(0, false), (0, false)]) (GA 0) &&
    baseEq bs (wv GM GMi surjB) (GA 1)) = true := by
  quickRfl

theorem kSig : (!baseEq bs (GM 1) (fun q => q) &&
    !baseEq bs (wv GM GMi sig2W) (fun q => q) &&
    !baseEq bs (wv GM GMi sig2W) (GM 1) &&
    !baseEq bs (wv GM GMi sig2W) (wv GM GMi [(1, true), (1, true)])) = true := by
  quickRfl

theorem kTabA : (baseEq bs (fun q => GA 0 (GA 0 q)) (fun q => q) &&
    !baseEq bs (GA 0) (fun q => q)) = true := by
  quickRfl

theorem kST : allN 3 (fun j => bAnd(permOK 820 10 (mask 10) (820 * 10) (ST j) (STI j),
    bAnd(inPU (ST j), baseEq bs (GS j) (wG GM GMi sW j)))) = true := by
  quickRfl

theorem kKT : kTree KT 10 (mask 10) 8 255 bs 128 3 GS = true := by quickRfl

end CertificateChecks.KernelU43Mod

end
