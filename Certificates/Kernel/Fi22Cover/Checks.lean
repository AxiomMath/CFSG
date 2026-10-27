module

public import Certificates.Kernel.Fi22Cover.Enum
public import Certificates.Kernel.Fi22Cover.Gens
public import Certificates.Kernel.Fi22Cover.Words
public import Certificates.Kernel.Sporadic.Fi22.X2069P
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Data.Kernel.Fi22Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Cover

open CFSG.KC.Fi22Cover CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor

@[expose] noncomputable def siftP (G : Nat) : Bool :=
  siftK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) Fi22PC.LR Fi22PC.TRI Fi22PC.BP 6 0 G

theorem permS : allN 20 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem der : allN 17 (fun i => bAnd(lt (W.der.getD (Nat.add i 3) []) (Nat.add i 3),
    Nat.beq (S (Nat.add i 3)) (wd S SI (W.der.getD (Nat.add i 3) [])))) = true := by
  quickRfl

theorem wa : allN 2 (fun k => bAnd(lt (W.wa.getD k []) 20,
    Nat.beq (Fi22CGT.F k) (wd S SI (W.wa.getD k [])))) = true := by
  quickRfl

theorem siftS : allN 3 (fun j => bAnd(cn (S j), bAnd(pk (S j), siftP (S j)))) = true := by quickRfl

theorem siftE : allN 5 (fun k => bAnd(cn (E5B.G k), bAnd(pk (E5B.G k), siftP (E5B.G k)))) = true := by
  quickRfl

theorem siftQ : allN 4 (fun k => bAnd(cn (Q4B.G k), bAnd(pk (Q4B.G k), siftP (Q4B.G k)))) = true := by
  quickRfl

theorem elemE : elemK 5 E5B.G = true := by quickRfl

theorem elemQ : elemK 4 Q4B.G = true := by quickRfl

theorem normE : conjK (S 0) 5 E5B.G E5B.N E5B.T = true := by quickRfl

theorem normQ : conjK (S 1) 4 Q4B.G Q4B.N Q4B.T = true := by quickRfl

theorem normQ' : conjK (S 2) 4 Q4B.G Q4B.N Q4B.T = true := by quickRfl

theorem normQE : allN 4 (fun k => conjK (Q4B.G k) 5 E5B.G E5B.N E5B.T) = true := by quickRfl

end CertificateChecks.KernelFi22Cover

end
