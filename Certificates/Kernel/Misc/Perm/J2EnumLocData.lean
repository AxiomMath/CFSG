module

public import Certificates.Kernel.Misc.Perm.J2EnumData
public import Certificates.Data.Kernel.Misc.SetCodes
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelMisc.J2En.O3
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.o3Sets 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2En.B4
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.b4Sets 9

public section

namespace CertificateChecks.KernelMisc.J2En

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.SetCodes
open CertificateChecks.KernelMisc.J2C3 (I cm chunkK)
open CertificateChecks.KernelMisc.J2Fam (GA GV H1 HV)

@[expose] noncomputable def two7K (p : ℕ) : Bool :=
  Nat.beq (Nat.rec (motive := fun _ => ℕ → ℕ) (fun q => q) (fun _ ih q => ih (cm q q)) 7 p) I

@[expose] noncomputable def twoGK (ns : List ℕ) (p : ℕ) : Bool :=
  two7K p && ns.all fun n => two7K (cm p (cj n p))

@[expose] noncomputable def caK (p : ℕ) : Bool := !(two7K p) || memL VEK p

@[expose] noncomputable def naSetK (p : ℕ) : Bool :=
  permutesK 3 1 9 O3 p && permutesK 4 3 9 B4 p &&
    (!(fixesK 3 1 9 O3 p && fixesK 4 3 9 B4 p) || Nat.beq p I)

@[expose] noncomputable def naK (p : ℕ) : Bool :=
  naSetK p && (!(twoGK [GA 0, GA 1, H1] p) || memL VEK p)

@[expose] noncomputable def nvK (p : ℕ) : Bool := !(twoGK [GV 0, GV 1, HV] p) || memL VEK p

@[expose] noncomputable def caC : ℕ → Bool := chunkK 36 fun k => caK (lget CaP k)

@[expose] noncomputable def naC : ℕ → Bool := chunkK 72 fun k => naK (lget NaP k)

@[expose] noncomputable def nvC : ℕ → Bool := chunkK 90 fun k => nvK (lget NVP k)

end CertificateChecks.KernelMisc.J2En

end
