module

public import Certificates.Kernel.HN1408.Cent3Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cent3

open CFSG.KC.Enum CFSG.KS

theorem ch441603_rows : allN 1440 (rowK R RK) = true := by quickRfl

theorem ch441603_cnt : cntK R RT = true := by quickRfl

theorem ch441603_p5 : p5K P5 = true := by quickRfl

theorem ch441603_p3 : p3K P3 = true := by quickRfl

theorem ch441603_mGen : mGenK MG = true := by quickRfl

theorem ch441603_mEl : allN 60 (mElK E X) = true := by quickRfl

theorem ch441603_mTree : allN 60 (mTreeK E EP MG) = true := by quickRfl

theorem ch441603_mCl : allN 60 (mClK E ECl MG) = true := by quickRfl

theorem ch441603_mComm : allN 2 (mCommK E MC MG) = true := by quickRfl

theorem ch441603_wc : wcK R RT WC = true := by quickRfl

end CFSG.KD.HN1408.Cent3

end
