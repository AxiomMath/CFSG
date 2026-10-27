module

public import Certificates.Kernel.HN1408.SylDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words
public import Certificates.Kernel.HN1408.SylData

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.FixR

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.HNRecog

theorem s3_gen : yGenF sylow3Words Syl3.YG = true := by quickRfl
theorem s3_tree : yTreeF Syl3.YG Syl3.Y Syl3.YI Syl3.YP 2 9 = true := by quickRfl
theorem s3_clos : closF Syl3.YG Syl3.Y Syl3.C 2 9 = true := by quickRfl
theorem s3_dist : distF Syl3.Y Syl3.D 9 = true := by quickRfl
theorem s3_cov : covF Syl3.Y Syl3.W 9 wit3 = true := by quickRfl

theorem s5_clos : closF Fix7.YG Fix7.Y Syl5.C 3 125 = true := by quickRfl
theorem s5_dist : distF Fix7.Y Syl5.D 125 = true := by quickRfl
theorem s5_cov : covF Fix7.Y Syl5.W 125 wit5 = true := by quickRfl

theorem s7_gen : yGenF sylow7Words Syl7.YG = true := by quickRfl
theorem s7_tree : yTreeF Syl7.YG Syl7.Y Syl7.YI Syl7.YP 1 7 = true := by quickRfl
theorem s7_clos : closF Syl7.YG Syl7.Y Syl7.C 1 7 = true := by quickRfl
theorem s7_dist : distF Syl7.Y Syl7.D 7 = true := by quickRfl
theorem s7_cov : covF Syl7.Y Syl7.W 7 wit7 = true := by quickRfl

end CFSG.KD.HN1408.FixR

end
