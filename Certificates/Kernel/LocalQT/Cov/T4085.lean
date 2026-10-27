module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.Misc.HexFlat
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverCheck
meta import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.Misc.Perm.HexCmd

set_option maxRecDepth 400000

#ks_chars CFSG.KD.LQT.C4085.CT CFSG.QuasithinUnique.Ch1.HSCover.covText

#ks_chars CFSG.KD.LQT.C4085.HS CFSG.Sporadic.Schreier.hsStrongHex
#kmisc_hexflat CFSG.KD.LQT.C4085.HS CFSG.Sporadic.Schreier.hsStrongHex 4 3850 12 2
