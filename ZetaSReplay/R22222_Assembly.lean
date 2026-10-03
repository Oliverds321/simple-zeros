import R22222_Leaves0
import R22222_Leaves1
import R22222_Leaves2
import R22222_Leaves3
import R22222_Leaves4
import R22222_Leaves5
import R22222_Leaves6
import R22222_Leaves7
import R22222_Leaves8
import R22222_Leaves9
import R22222_Leaves10
import R22222_Leaves11
import R22222_Leaves12
import R22222_Leaves13
import R22222_Leaves14
import R22222_Leaves15
import R22222_Leaves16
import R22222_Leaves17
import R22222_Leaves18
import R22222_Leaves19
import R22222_Leaves20
import R22222_Leaves21
import R22222_Leaves22
import R22222_Leaves23
import R22222_Leaves24
import R22222_Leaves25
import R22222_Leaves26
import R22222_Leaves27
import R22222_Leaves28
import R22222_Leaves29
import R22222_Leaves30
import R22222_Leaves31
import R22222_Leaves32
import R22222_Leaves33
import R22222_Leaves34
import R22222_Leaves35
import R22222_Leaves36
import R22222_Leaves37
import R22222_Leaves38
import R22222_Leaves39
import R22222_Leaves40
import R22222_Leaves41
import R22222_Leaves42
import R22222_Leaves43
import R22222_Leaves44
import R22222_Leaves45
import R22222_Leaves46
import R22222_Leaves47
import R22222_Leaves48
import R22222_Leaves49

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2
namespace R22222

def T3938 : Node := Node.leaf L3938
theorem T3938_ok : Node.check D_R22222 T3938 [((163/32),(163/16)),((0),(405/64)),((0),(405/64)),((163/32),(163/16))] = true := Node.check_leaf_of _ _ _ L3938_ok
def T3937 : Node := Node.leaf L3937
theorem T3937_ok : Node.check D_R22222 T3937 [((163/32),(163/16)),((405/128),(405/64)),((0),(405/64)),((0),(163/32))] = true := Node.check_leaf_of _ _ _ L3937_ok
def T3936 : Node := Node.leaf L3936
theorem T3936_ok : Node.check D_R22222 T3936 [((163/32),(163/16)),((0),(405/128)),((405/128),(405/64)),((0),(163/32))] = true := Node.check_leaf_of _ _ _ L3936_ok
def T3935 : Node := Node.leaf L3935
theorem T3935_ok : Node.check D_R22222 T3935 [((489/64),(163/16)),((0),(405/128)),((0),(405/128)),((163/64),(163/32))] = true := Node.check_leaf_of _ _ _ L3935_ok
def T3934 : Node := Node.leaf L3934
theorem T3934_ok : Node.check D_R22222 T3934 [((489/64),(163/16)),((405/256),(405/128)),((0),(405/128)),((0),(163/64))] = true := Node.check_leaf_of _ _ _ L3934_ok
def T3933 : Node := Node.leaf L3933
theorem T3933_ok : Node.check D_R22222 T3933 [((489/64),(163/16)),((0),(405/256)),((405/256),(405/128)),((0),(163/64))] = true := Node.check_leaf_of _ _ _ L3933_ok
def T3932 : Node := Node.leaf L3932
theorem T3932_ok : Node.check D_R22222 T3932 [((1141/128),(163/16)),((0),(405/256)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3932_ok
def T3931 : Node := Node.leaf L3931
theorem T3931_ok : Node.check D_R22222 T3931 [((1141/128),(163/16)),((405/512),(405/256)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3931_ok
def T3930 : Node := Node.leaf L3930
theorem T3930_ok : Node.check D_R22222 T3930 [((1141/128),(163/16)),((0),(405/512)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3930_ok
def T3929 : Node := Node.split 1 T3930 T3931
theorem T3929_ok : Node.check D_R22222 T3929 [((1141/128),(163/16)),((0),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3930_ok T3931_ok
def T3928 : Node := Node.split 3 T3929 T3932
theorem T3928_ok : Node.check D_R22222 T3928 [((1141/128),(163/16)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3929_ok T3932_ok
def T3927 : Node := Node.leaf L3927
theorem T3927_ok : Node.check D_R22222 T3927 [((489/64),(1141/128)),((405/512),(405/256)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3927_ok
def T3926 : Node := Node.leaf L3926
theorem T3926_ok : Node.check D_R22222 T3926 [((489/64),(1141/128)),((0),(405/512)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3926_ok
def T3925 : Node := Node.split 1 T3926 T3927
theorem T3925_ok : Node.check D_R22222 T3925 [((489/64),(1141/128)),((0),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3926_ok T3927_ok
def T3924 : Node := Node.leaf L3924
theorem T3924_ok : Node.check D_R22222 T3924 [((489/64),(1141/128)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3924_ok
def T3923 : Node := Node.leaf L3923
theorem T3923_ok : Node.check D_R22222 T3923 [((489/64),(1141/128)),((405/512),(405/256)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3923_ok
def T3922 : Node := Node.split 2 T3923 T3924
theorem T3922_ok : Node.check D_R22222 T3922 [((489/64),(1141/128)),((405/512),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3923_ok T3924_ok
def T3921 : Node := Node.leaf L3921
theorem T3921_ok : Node.check D_R22222 T3921 [((489/64),(1141/128)),((0),(405/512)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3921_ok
def T3920 : Node := Node.split 1 T3921 T3922
theorem T3920_ok : Node.check D_R22222 T3920 [((489/64),(1141/128)),((0),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3921_ok T3922_ok
def T3919 : Node := Node.split 3 T3920 T3925
theorem T3919_ok : Node.check D_R22222 T3919 [((489/64),(1141/128)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3920_ok T3925_ok
def T3918 : Node := Node.split 0 T3919 T3928
theorem T3918_ok : Node.check D_R22222 T3918 [((489/64),(163/16)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3919_ok T3928_ok
def T3917 : Node := Node.split 2 T3918 T3933
theorem T3917_ok : Node.check D_R22222 T3917 [((489/64),(163/16)),((0),(405/256)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3918_ok T3933_ok
def T3916 : Node := Node.split 1 T3917 T3934
theorem T3916_ok : Node.check D_R22222 T3916 [((489/64),(163/16)),((0),(405/128)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3917_ok T3934_ok
def T3915 : Node := Node.split 3 T3916 T3935
theorem T3915_ok : Node.check D_R22222 T3915 [((489/64),(163/16)),((0),(405/128)),((0),(405/128)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3916_ok T3935_ok
def T3914 : Node := Node.leaf L3914
theorem T3914_ok : Node.check D_R22222 T3914 [((163/32),(489/64)),((405/256),(405/128)),((0),(405/128)),((163/64),(163/32))] = true := Node.check_leaf_of _ _ _ L3914_ok
def T3913 : Node := Node.leaf L3913
theorem T3913_ok : Node.check D_R22222 T3913 [((163/32),(489/64)),((0),(405/256)),((405/256),(405/128)),((163/64),(163/32))] = true := Node.check_leaf_of _ _ _ L3913_ok
def T3912 : Node := Node.leaf L3912
theorem T3912_ok : Node.check D_R22222 T3912 [((815/128),(489/64)),((0),(405/256)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3912_ok
def T3911 : Node := Node.leaf L3911
theorem T3911_ok : Node.check D_R22222 T3911 [((815/128),(489/64)),((405/512),(405/256)),((0),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3911_ok
def T3910 : Node := Node.leaf L3910
theorem T3910_ok : Node.check D_R22222 T3910 [((815/128),(489/64)),((0),(405/512)),((0),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3910_ok
def T3909 : Node := Node.split 1 T3910 T3911
theorem T3909_ok : Node.check D_R22222 T3909 [((815/128),(489/64)),((0),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3910_ok T3911_ok
def T3908 : Node := Node.split 3 T3909 T3912
theorem T3908_ok : Node.check D_R22222 T3908 [((815/128),(489/64)),((0),(405/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3909_ok T3912_ok
def T3907 : Node := Node.leaf L3907
theorem T3907_ok : Node.check D_R22222 T3907 [((163/32),(815/128)),((405/512),(405/256)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3907_ok
def T3906 : Node := Node.leaf L3906
theorem T3906_ok : Node.check D_R22222 T3906 [((163/32),(815/128)),((0),(405/512)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3906_ok
def T3905 : Node := Node.split 1 T3906 T3907
theorem T3905_ok : Node.check D_R22222 T3905 [((163/32),(815/128)),((0),(405/256)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3906_ok T3907_ok
def T3904 : Node := Node.leaf L3904
theorem T3904_ok : Node.check D_R22222 T3904 [((163/32),(815/128)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3904_ok
def T3903 : Node := Node.leaf L3903
theorem T3903_ok : Node.check D_R22222 T3903 [((163/32),(815/128)),((405/512),(405/256)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3903_ok
def T3902 : Node := Node.split 2 T3903 T3904
theorem T3902_ok : Node.check D_R22222 T3902 [((163/32),(815/128)),((405/512),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3903_ok T3904_ok
def T3901 : Node := Node.leaf L3901
theorem T3901_ok : Node.check D_R22222 T3901 [((163/32),(815/128)),((0),(405/512)),((0),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3901_ok
def T3900 : Node := Node.split 1 T3901 T3902
theorem T3900_ok : Node.check D_R22222 T3900 [((163/32),(815/128)),((0),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3901_ok T3902_ok
def T3899 : Node := Node.split 3 T3900 T3905
theorem T3899_ok : Node.check D_R22222 T3899 [((163/32),(815/128)),((0),(405/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3900_ok T3905_ok
def T3898 : Node := Node.split 0 T3899 T3908
theorem T3898_ok : Node.check D_R22222 T3898 [((163/32),(489/64)),((0),(405/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3899_ok T3908_ok
def T3897 : Node := Node.split 2 T3898 T3913
theorem T3897_ok : Node.check D_R22222 T3897 [((163/32),(489/64)),((0),(405/256)),((0),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3898_ok T3913_ok
def T3896 : Node := Node.split 1 T3897 T3914
theorem T3896_ok : Node.check D_R22222 T3896 [((163/32),(489/64)),((0),(405/128)),((0),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3897_ok T3914_ok
def T3895 : Node := Node.leaf L3895
theorem T3895_ok : Node.check D_R22222 T3895 [((163/32),(489/64)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/64))] = true := Node.check_leaf_of _ _ _ L3895_ok
def T3894 : Node := Node.leaf L3894
theorem T3894_ok : Node.check D_R22222 T3894 [((815/128),(489/64)),((405/256),(405/128)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3894_ok
def T3893 : Node := Node.leaf L3893
theorem T3893_ok : Node.check D_R22222 T3893 [((815/128),(489/64)),((1215/512),(405/128)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3893_ok
def T3892 : Node := Node.leaf L3892
theorem T3892_ok : Node.check D_R22222 T3892 [((815/128),(489/64)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3892_ok
def T3891 : Node := Node.leaf L3891
theorem T3891_ok : Node.check D_R22222 T3891 [((815/128),(489/64)),((405/256),(1215/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3891_ok
def T3890 : Node := Node.split 2 T3891 T3892
theorem T3890_ok : Node.check D_R22222 T3890 [((815/128),(489/64)),((405/256),(1215/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3891_ok T3892_ok
def T3889 : Node := Node.split 1 T3890 T3893
theorem T3889_ok : Node.check D_R22222 T3889 [((815/128),(489/64)),((405/256),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3890_ok T3893_ok
def T3888 : Node := Node.split 3 T3889 T3894
theorem T3888_ok : Node.check D_R22222 T3888 [((815/128),(489/64)),((405/256),(405/128)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3889_ok T3894_ok
def T3887 : Node := Node.leaf L3887
theorem T3887_ok : Node.check D_R22222 T3887 [((163/32),(815/128)),((1215/512),(405/128)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3887_ok
def T3886 : Node := Node.leaf L3886
theorem T3886_ok : Node.check D_R22222 T3886 [((163/32),(815/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3886_ok
def T3885 : Node := Node.leaf L3885
theorem T3885_ok : Node.check D_R22222 T3885 [((163/32),(815/128)),((405/256),(1215/512)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3885_ok
def T3884 : Node := Node.split 2 T3885 T3886
theorem T3884_ok : Node.check D_R22222 T3884 [((163/32),(815/128)),((405/256),(1215/512)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3885_ok T3886_ok
def T3883 : Node := Node.split 1 T3884 T3887
theorem T3883_ok : Node.check D_R22222 T3883 [((163/32),(815/128)),((405/256),(405/128)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3884_ok T3887_ok
def T3882 : Node := Node.leaf L3882
theorem T3882_ok : Node.check D_R22222 T3882 [((163/32),(815/128)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3882_ok
def T3881 : Node := Node.leaf L3881
theorem T3881_ok : Node.check D_R22222 T3881 [((163/32),(815/128)),((1215/512),(405/128)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3881_ok
def T3880 : Node := Node.split 2 T3881 T3882
theorem T3880_ok : Node.check D_R22222 T3880 [((163/32),(815/128)),((1215/512),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3881_ok T3882_ok
def T3879 : Node := Node.leaf L3879
theorem T3879_ok : Node.check D_R22222 T3879 [((1467/256),(815/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3879_ok
def T3878 : Node := Node.leaf L3878
theorem T3878_ok : Node.check D_R22222 T3878 [((1467/256),(815/128)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3878_ok
def T3877 : Node := Node.split 3 T3878 T3879
theorem T3877_ok : Node.check D_R22222 T3877 [((1467/256),(815/128)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3878_ok T3879_ok
def T3876 : Node := Node.leaf L3876
theorem T3876_ok : Node.check D_R22222 T3876 [((163/32),(1467/256)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3876_ok
def T3875 : Node := Node.leaf L3875
theorem T3875_ok : Node.check D_R22222 T3875 [((163/32),(1467/256)),((405/256),(2025/1024)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3875_ok
def T3874 : Node := Node.split 1 T3875 T3876
theorem T3874_ok : Node.check D_R22222 T3874 [((163/32),(1467/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3875_ok T3876_ok
def T3873 : Node := Node.leaf L3873
theorem T3873_ok : Node.check D_R22222 T3873 [((163/32),(1467/256)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3873_ok
def T3872 : Node := Node.split 3 T3873 T3874
theorem T3872_ok : Node.check D_R22222 T3872 [((163/32),(1467/256)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3873_ok T3874_ok
def T3871 : Node := Node.split 0 T3872 T3877
theorem T3871_ok : Node.check D_R22222 T3871 [((163/32),(815/128)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3872_ok T3877_ok
def T3870 : Node := Node.leaf L3870
theorem T3870_ok : Node.check D_R22222 T3870 [((163/32),(815/128)),((405/256),(1215/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3870_ok
def T3869 : Node := Node.split 2 T3870 T3871
theorem T3869_ok : Node.check D_R22222 T3869 [((163/32),(815/128)),((405/256),(1215/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3870_ok T3871_ok
def T3868 : Node := Node.split 1 T3869 T3880
theorem T3868_ok : Node.check D_R22222 T3868 [((163/32),(815/128)),((405/256),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3869_ok T3880_ok
def T3867 : Node := Node.split 3 T3868 T3883
theorem T3867_ok : Node.check D_R22222 T3867 [((163/32),(815/128)),((405/256),(405/128)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3868_ok T3883_ok
def T3866 : Node := Node.split 0 T3867 T3888
theorem T3866_ok : Node.check D_R22222 T3866 [((163/32),(489/64)),((405/256),(405/128)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3867_ok T3888_ok
def T3865 : Node := Node.split 2 T3866 T3895
theorem T3865_ok : Node.check D_R22222 T3865 [((163/32),(489/64)),((405/256),(405/128)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3866_ok T3895_ok
def T3864 : Node := Node.leaf L3864
theorem T3864_ok : Node.check D_R22222 T3864 [((815/128),(489/64)),((0),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3864_ok
def T3863 : Node := Node.leaf L3863
theorem T3863_ok : Node.check D_R22222 T3863 [((815/128),(489/64)),((405/512),(405/256)),((405/256),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3863_ok
def T3862 : Node := Node.leaf L3862
theorem T3862_ok : Node.check D_R22222 T3862 [((815/128),(489/64)),((0),(405/512)),((405/256),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3862_ok
def T3861 : Node := Node.split 1 T3862 T3863
theorem T3861_ok : Node.check D_R22222 T3861 [((815/128),(489/64)),((0),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3862_ok T3863_ok
def T3860 : Node := Node.split 3 T3861 T3864
theorem T3860_ok : Node.check D_R22222 T3860 [((815/128),(489/64)),((0),(405/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3861_ok T3864_ok
def T3859 : Node := Node.leaf L3859
theorem T3859_ok : Node.check D_R22222 T3859 [((163/32),(815/128)),((405/512),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3859_ok
def T3858 : Node := Node.leaf L3858
theorem T3858_ok : Node.check D_R22222 T3858 [((163/32),(815/128)),((0),(405/512)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3858_ok
def T3857 : Node := Node.split 1 T3858 T3859
theorem T3857_ok : Node.check D_R22222 T3857 [((163/32),(815/128)),((0),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3858_ok T3859_ok
def T3856 : Node := Node.leaf L3856
theorem T3856_ok : Node.check D_R22222 T3856 [((163/32),(815/128)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3856_ok
def T3855 : Node := Node.leaf L3855
theorem T3855_ok : Node.check D_R22222 T3855 [((1467/256),(815/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3855_ok
def T3854 : Node := Node.leaf L3854
theorem T3854_ok : Node.check D_R22222 T3854 [((1467/256),(815/128)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3854_ok
def T3853 : Node := Node.split 3 T3854 T3855
theorem T3853_ok : Node.check D_R22222 T3853 [((1467/256),(815/128)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3854_ok T3855_ok
def T3852 : Node := Node.leaf L3852
theorem T3852_ok : Node.check D_R22222 T3852 [((163/32),(1467/256)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3852_ok
def T3851 : Node := Node.leaf L3851
theorem T3851_ok : Node.check D_R22222 T3851 [((163/32),(1467/256)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3851_ok
def T3850 : Node := Node.split 1 T3851 T3852
theorem T3850_ok : Node.check D_R22222 T3850 [((163/32),(1467/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3851_ok T3852_ok
def T3849 : Node := Node.leaf L3849
theorem T3849_ok : Node.check D_R22222 T3849 [((163/32),(1467/256)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3849_ok
def T3848 : Node := Node.split 3 T3849 T3850
theorem T3848_ok : Node.check D_R22222 T3848 [((163/32),(1467/256)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3849_ok T3850_ok
def T3847 : Node := Node.split 0 T3848 T3853
theorem T3847_ok : Node.check D_R22222 T3847 [((163/32),(815/128)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3848_ok T3853_ok
def T3846 : Node := Node.split 2 T3847 T3856
theorem T3846_ok : Node.check D_R22222 T3846 [((163/32),(815/128)),((405/512),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3847_ok T3856_ok
def T3845 : Node := Node.leaf L3845
theorem T3845_ok : Node.check D_R22222 T3845 [((163/32),(815/128)),((0),(405/512)),((405/256),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3845_ok
def T3844 : Node := Node.split 1 T3845 T3846
theorem T3844_ok : Node.check D_R22222 T3844 [((163/32),(815/128)),((0),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3845_ok T3846_ok
def T3843 : Node := Node.split 3 T3844 T3857
theorem T3843_ok : Node.check D_R22222 T3843 [((163/32),(815/128)),((0),(405/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3844_ok T3857_ok
def T3842 : Node := Node.split 0 T3843 T3860
theorem T3842_ok : Node.check D_R22222 T3842 [((163/32),(489/64)),((0),(405/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3843_ok T3860_ok
def T3841 : Node := Node.leaf L3841
theorem T3841_ok : Node.check D_R22222 T3841 [((815/128),(489/64)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3841_ok
def T3840 : Node := Node.leaf L3840
theorem T3840_ok : Node.check D_R22222 T3840 [((815/128),(489/64)),((405/512),(405/256)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3840_ok
def T3839 : Node := Node.split 2 T3840 T3841
theorem T3839_ok : Node.check D_R22222 T3839 [((815/128),(489/64)),((405/512),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3840_ok T3841_ok
def T3838 : Node := Node.leaf L3838
theorem T3838_ok : Node.check D_R22222 T3838 [((815/128),(489/64)),((0),(405/512)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3838_ok
def T3837 : Node := Node.split 1 T3838 T3839
theorem T3837_ok : Node.check D_R22222 T3837 [((815/128),(489/64)),((0),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3838_ok T3839_ok
def T3836 : Node := Node.leaf L3836
theorem T3836_ok : Node.check D_R22222 T3836 [((1793/256),(489/64)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3836_ok
def T3835 : Node := Node.leaf L3835
theorem T3835_ok : Node.check D_R22222 T3835 [((1793/256),(489/64)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3835_ok
def T3834 : Node := Node.split 3 T3835 T3836
theorem T3834_ok : Node.check D_R22222 T3834 [((1793/256),(489/64)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3835_ok T3836_ok
def T3833 : Node := Node.leaf L3833
theorem T3833_ok : Node.check D_R22222 T3833 [((815/128),(1793/256)),((1215/1024),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3833_ok
def T3832 : Node := Node.leaf L3832
theorem T3832_ok : Node.check D_R22222 T3832 [((815/128),(1793/256)),((405/512),(1215/1024)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3832_ok
def T3831 : Node := Node.split 1 T3832 T3833
theorem T3831_ok : Node.check D_R22222 T3831 [((815/128),(1793/256)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3832_ok T3833_ok
def T3830 : Node := Node.leaf L3830
theorem T3830_ok : Node.check D_R22222 T3830 [((815/128),(1793/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3830_ok
def T3829 : Node := Node.split 3 T3830 T3831
theorem T3829_ok : Node.check D_R22222 T3829 [((815/128),(1793/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3830_ok T3831_ok
def T3828 : Node := Node.split 0 T3829 T3834
theorem T3828_ok : Node.check D_R22222 T3828 [((815/128),(489/64)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3829_ok T3834_ok
def T3827 : Node := Node.leaf L3827
theorem T3827_ok : Node.check D_R22222 T3827 [((815/128),(489/64)),((405/512),(405/256)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3827_ok
def T3826 : Node := Node.split 2 T3827 T3828
theorem T3826_ok : Node.check D_R22222 T3826 [((815/128),(489/64)),((405/512),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3827_ok T3828_ok
def T3825 : Node := Node.leaf L3825
theorem T3825_ok : Node.check D_R22222 T3825 [((815/128),(489/64)),((0),(405/512)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3825_ok
def T3824 : Node := Node.split 1 T3825 T3826
theorem T3824_ok : Node.check D_R22222 T3824 [((815/128),(489/64)),((0),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3825_ok T3826_ok
def T3823 : Node := Node.split 3 T3824 T3837
theorem T3823_ok : Node.check D_R22222 T3823 [((815/128),(489/64)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3824_ok T3837_ok
def T3822 : Node := Node.leaf L3822
theorem T3822_ok : Node.check D_R22222 T3822 [((1467/256),(815/128)),((405/512),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3822_ok
def T3821 : Node := Node.leaf L3821
theorem T3821_ok : Node.check D_R22222 T3821 [((1467/256),(815/128)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L3821_ok
def T3820 : Node := Node.split 3 T3821 T3822
theorem T3820_ok : Node.check D_R22222 T3820 [((1467/256),(815/128)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3821_ok T3822_ok
def T3819 : Node := Node.leaf L3819
theorem T3819_ok : Node.check D_R22222 T3819 [((163/32),(1467/256)),((1215/1024),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3819_ok
def T3818 : Node := Node.leaf L3818
theorem T3818_ok : Node.check D_R22222 T3818 [((163/32),(1467/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3818_ok
def T3817 : Node := Node.leaf L3817
theorem T3817_ok : Node.check D_R22222 T3817 [((163/32),(1467/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3817_ok
def T3816 : Node := Node.split 2 T3817 T3818
theorem T3816_ok : Node.check D_R22222 T3816 [((163/32),(1467/256)),((405/512),(1215/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3817_ok T3818_ok
def T3815 : Node := Node.split 1 T3816 T3819
theorem T3815_ok : Node.check D_R22222 T3815 [((163/32),(1467/256)),((405/512),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3816_ok T3819_ok
def T3814 : Node := Node.leaf L3814
theorem T3814_ok : Node.check D_R22222 T3814 [((163/32),(1467/256)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L3814_ok
def T3813 : Node := Node.split 3 T3814 T3815
theorem T3813_ok : Node.check D_R22222 T3813 [((163/32),(1467/256)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3814_ok T3815_ok
def T3812 : Node := Node.split 0 T3813 T3820
theorem T3812_ok : Node.check D_R22222 T3812 [((163/32),(815/128)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3813_ok T3820_ok
def T3811 : Node := Node.leaf L3811
theorem T3811_ok : Node.check D_R22222 T3811 [((163/32),(815/128)),((405/512),(405/256)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3811_ok
def T3810 : Node := Node.split 2 T3811 T3812
theorem T3810_ok : Node.check D_R22222 T3810 [((163/32),(815/128)),((405/512),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3811_ok T3812_ok
def T3809 : Node := Node.leaf L3809
theorem T3809_ok : Node.check D_R22222 T3809 [((163/32),(815/128)),((0),(405/512)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3809_ok
def T3808 : Node := Node.split 1 T3809 T3810
theorem T3808_ok : Node.check D_R22222 T3808 [((163/32),(815/128)),((0),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3809_ok T3810_ok
def T3807 : Node := Node.leaf L3807
theorem T3807_ok : Node.check D_R22222 T3807 [((1467/256),(815/128)),((1215/1024),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3807_ok
def T3806 : Node := Node.leaf L3806
theorem T3806_ok : Node.check D_R22222 T3806 [((1467/256),(815/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3806_ok
def T3805 : Node := Node.leaf L3805
theorem T3805_ok : Node.check D_R22222 T3805 [((3097/512),(815/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3805_ok
def T3804 : Node := Node.leaf L3804
theorem T3804_ok : Node.check D_R22222 T3804 [((1467/256),(3097/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3804_ok
def T3803 : Node := Node.split 0 T3804 T3805
theorem T3803_ok : Node.check D_R22222 T3803 [((1467/256),(815/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3804_ok T3805_ok
def T3802 : Node := Node.split 2 T3803 T3806
theorem T3802_ok : Node.check D_R22222 T3802 [((1467/256),(815/128)),((405/512),(1215/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3803_ok T3806_ok
def T3801 : Node := Node.split 1 T3802 T3807
theorem T3801_ok : Node.check D_R22222 T3801 [((1467/256),(815/128)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3802_ok T3807_ok
def T3800 : Node := Node.leaf L3800
theorem T3800_ok : Node.check D_R22222 T3800 [((1467/256),(815/128)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3800_ok
def T3799 : Node := Node.split 3 T3800 T3801
theorem T3799_ok : Node.check D_R22222 T3799 [((1467/256),(815/128)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3800_ok T3801_ok
def T3798 : Node := Node.leaf L3798
theorem T3798_ok : Node.check D_R22222 T3798 [((163/32),(1467/256)),((1215/1024),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3798_ok
def T3797 : Node := Node.leaf L3797
theorem T3797_ok : Node.check D_R22222 T3797 [((163/32),(1467/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3797_ok
def T3796 : Node := Node.leaf L3796
theorem T3796_ok : Node.check D_R22222 T3796 [((2771/512),(1467/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3796_ok
def T3795 : Node := Node.leaf L3795
theorem T3795_ok : Node.check D_R22222 T3795 [((5379/1024),(2771/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3795_ok
def T3794 : Node := Node.leaf L3794
theorem T3794_ok : Node.check D_R22222 T3794 [((163/32),(5379/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L3794_ok
def T3793 : Node := Node.leaf L3793
theorem T3793_ok : Node.check D_R22222 T3793 [((163/32),(5379/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L3793_ok
def T3792 : Node := Node.leaf L3792
theorem T3792_ok : Node.check D_R22222 T3792 [((163/32),(5379/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L3792_ok
def T3791 : Node := Node.leaf L3791
theorem T3791_ok : Node.check D_R22222 T3791 [((163/32),(5379/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L3791_ok
def T3790 : Node := Node.split 2 T3791 T3792
theorem T3790_ok : Node.check D_R22222 T3790 [((163/32),(5379/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3791_ok T3792_ok
def T3789 : Node := Node.split 1 T3790 T3793
theorem T3789_ok : Node.check D_R22222 T3789 [((163/32),(5379/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3790_ok T3793_ok
def T3788 : Node := Node.split 3 T3789 T3794
theorem T3788_ok : Node.check D_R22222 T3788 [((163/32),(5379/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3789_ok T3794_ok
def T3787 : Node := Node.split 0 T3788 T3795
theorem T3787_ok : Node.check D_R22222 T3787 [((163/32),(2771/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3788_ok T3795_ok
def T3786 : Node := Node.leaf L3786
theorem T3786_ok : Node.check D_R22222 T3786 [((163/32),(2771/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3786_ok
def T3785 : Node := Node.split 2 T3786 T3787
theorem T3785_ok : Node.check D_R22222 T3785 [((163/32),(2771/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3786_ok T3787_ok
def T3784 : Node := Node.leaf L3784
theorem T3784_ok : Node.check D_R22222 T3784 [((163/32),(2771/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3784_ok
def T3783 : Node := Node.split 1 T3784 T3785
theorem T3783_ok : Node.check D_R22222 T3783 [((163/32),(2771/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3784_ok T3785_ok
def T3782 : Node := Node.leaf L3782
theorem T3782_ok : Node.check D_R22222 T3782 [((163/32),(2771/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L3782_ok
def T3781 : Node := Node.split 3 T3782 T3783
theorem T3781_ok : Node.check D_R22222 T3781 [((163/32),(2771/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3782_ok T3783_ok
def T3780 : Node := Node.split 0 T3781 T3796
theorem T3780_ok : Node.check D_R22222 T3780 [((163/32),(1467/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3781_ok T3796_ok
def T3779 : Node := Node.split 2 T3780 T3797
theorem T3779_ok : Node.check D_R22222 T3779 [((163/32),(1467/256)),((405/512),(1215/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3780_ok T3797_ok
def T3778 : Node := Node.split 1 T3779 T3798
theorem T3778_ok : Node.check D_R22222 T3778 [((163/32),(1467/256)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3779_ok T3798_ok
def T3777 : Node := Node.leaf L3777
theorem T3777_ok : Node.check D_R22222 T3777 [((163/32),(1467/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3777_ok
def T3776 : Node := Node.split 3 T3777 T3778
theorem T3776_ok : Node.check D_R22222 T3776 [((163/32),(1467/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3777_ok T3778_ok
def T3775 : Node := Node.split 0 T3776 T3799
theorem T3775_ok : Node.check D_R22222 T3775 [((163/32),(815/128)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3776_ok T3799_ok
def T3774 : Node := Node.leaf L3774
theorem T3774_ok : Node.check D_R22222 T3774 [((163/32),(815/128)),((405/512),(405/256)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3774_ok
def T3773 : Node := Node.split 2 T3774 T3775
theorem T3773_ok : Node.check D_R22222 T3773 [((163/32),(815/128)),((405/512),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3774_ok T3775_ok
def T3772 : Node := Node.leaf L3772
theorem T3772_ok : Node.check D_R22222 T3772 [((163/32),(815/128)),((0),(405/512)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3772_ok
def T3771 : Node := Node.split 1 T3772 T3773
theorem T3771_ok : Node.check D_R22222 T3771 [((163/32),(815/128)),((0),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3772_ok T3773_ok
def T3770 : Node := Node.split 3 T3771 T3808
theorem T3770_ok : Node.check D_R22222 T3770 [((163/32),(815/128)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3771_ok T3808_ok
def T3769 : Node := Node.split 0 T3770 T3823
theorem T3769_ok : Node.check D_R22222 T3769 [((163/32),(489/64)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3770_ok T3823_ok
def T3768 : Node := Node.split 2 T3769 T3842
theorem T3768_ok : Node.check D_R22222 T3768 [((163/32),(489/64)),((0),(405/256)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3769_ok T3842_ok
def T3767 : Node := Node.split 1 T3768 T3865
theorem T3767_ok : Node.check D_R22222 T3767 [((163/32),(489/64)),((0),(405/128)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3768_ok T3865_ok
def T3766 : Node := Node.split 3 T3767 T3896
theorem T3766_ok : Node.check D_R22222 T3766 [((163/32),(489/64)),((0),(405/128)),((0),(405/128)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3767_ok T3896_ok
def T3765 : Node := Node.split 0 T3766 T3915
theorem T3765_ok : Node.check D_R22222 T3765 [((163/32),(163/16)),((0),(405/128)),((0),(405/128)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3766_ok T3915_ok
def T3764 : Node := Node.split 2 T3765 T3936
theorem T3764_ok : Node.check D_R22222 T3764 [((163/32),(163/16)),((0),(405/128)),((0),(405/64)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3765_ok T3936_ok
def T3763 : Node := Node.split 1 T3764 T3937
theorem T3763_ok : Node.check D_R22222 T3763 [((163/32),(163/16)),((0),(405/64)),((0),(405/64)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3764_ok T3937_ok
def T3762 : Node := Node.split 3 T3763 T3938
theorem T3762_ok : Node.check D_R22222 T3762 [((163/32),(163/16)),((0),(405/64)),((0),(405/64)),((0),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3763_ok T3938_ok
def T3761 : Node := Node.leaf L3761
theorem T3761_ok : Node.check D_R22222 T3761 [((0),(163/32)),((405/128),(405/64)),((0),(405/64)),((163/32),(163/16))] = true := Node.check_leaf_of _ _ _ L3761_ok
def T3760 : Node := Node.leaf L3760
theorem T3760_ok : Node.check D_R22222 T3760 [((0),(163/32)),((0),(405/128)),((405/128),(405/64)),((163/32),(163/16))] = true := Node.check_leaf_of _ _ _ L3760_ok
def T3759 : Node := Node.leaf L3759
theorem T3759_ok : Node.check D_R22222 T3759 [((163/64),(163/32)),((0),(405/128)),((0),(405/128)),((489/64),(163/16))] = true := Node.check_leaf_of _ _ _ L3759_ok
def T3758 : Node := Node.leaf L3758
theorem T3758_ok : Node.check D_R22222 T3758 [((163/64),(163/32)),((405/256),(405/128)),((0),(405/128)),((163/32),(489/64))] = true := Node.check_leaf_of _ _ _ L3758_ok
def T3757 : Node := Node.leaf L3757
theorem T3757_ok : Node.check D_R22222 T3757 [((163/64),(163/32)),((0),(405/256)),((405/256),(405/128)),((163/32),(489/64))] = true := Node.check_leaf_of _ _ _ L3757_ok
def T3756 : Node := Node.leaf L3756
theorem T3756_ok : Node.check D_R22222 T3756 [((489/128),(163/32)),((0),(405/256)),((0),(405/256)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3756_ok
def T3755 : Node := Node.leaf L3755
theorem T3755_ok : Node.check D_R22222 T3755 [((489/128),(163/32)),((405/512),(405/256)),((0),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3755_ok
def T3754 : Node := Node.leaf L3754
theorem T3754_ok : Node.check D_R22222 T3754 [((489/128),(163/32)),((0),(405/512)),((0),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3754_ok
def T3753 : Node := Node.split 1 T3754 T3755
theorem T3753_ok : Node.check D_R22222 T3753 [((489/128),(163/32)),((0),(405/256)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3754_ok T3755_ok
def T3752 : Node := Node.split 3 T3753 T3756
theorem T3752_ok : Node.check D_R22222 T3752 [((489/128),(163/32)),((0),(405/256)),((0),(405/256)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3753_ok T3756_ok
def T3751 : Node := Node.leaf L3751
theorem T3751_ok : Node.check D_R22222 T3751 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/256)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3751_ok
def T3750 : Node := Node.leaf L3750
theorem T3750_ok : Node.check D_R22222 T3750 [((163/64),(489/128)),((0),(405/512)),((0),(405/256)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3750_ok
def T3749 : Node := Node.split 1 T3750 T3751
theorem T3749_ok : Node.check D_R22222 T3749 [((163/64),(489/128)),((0),(405/256)),((0),(405/256)),((815/128),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3750_ok T3751_ok
def T3748 : Node := Node.leaf L3748
theorem T3748_ok : Node.check D_R22222 T3748 [((163/64),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3748_ok
def T3747 : Node := Node.leaf L3747
theorem T3747_ok : Node.check D_R22222 T3747 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/512)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3747_ok
def T3746 : Node := Node.split 2 T3747 T3748
theorem T3746_ok : Node.check D_R22222 T3746 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3747_ok T3748_ok
def T3745 : Node := Node.leaf L3745
theorem T3745_ok : Node.check D_R22222 T3745 [((163/64),(489/128)),((0),(405/512)),((0),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3745_ok
def T3744 : Node := Node.split 1 T3745 T3746
theorem T3744_ok : Node.check D_R22222 T3744 [((163/64),(489/128)),((0),(405/256)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3745_ok T3746_ok
def T3743 : Node := Node.split 3 T3744 T3749
theorem T3743_ok : Node.check D_R22222 T3743 [((163/64),(489/128)),((0),(405/256)),((0),(405/256)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3744_ok T3749_ok
def T3742 : Node := Node.split 0 T3743 T3752
theorem T3742_ok : Node.check D_R22222 T3742 [((163/64),(163/32)),((0),(405/256)),((0),(405/256)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3743_ok T3752_ok
def T3741 : Node := Node.split 2 T3742 T3757
theorem T3741_ok : Node.check D_R22222 T3741 [((163/64),(163/32)),((0),(405/256)),((0),(405/128)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3742_ok T3757_ok
def T3740 : Node := Node.split 1 T3741 T3758
theorem T3740_ok : Node.check D_R22222 T3740 [((163/64),(163/32)),((0),(405/128)),((0),(405/128)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3741_ok T3758_ok
def T3739 : Node := Node.split 3 T3740 T3759
theorem T3739_ok : Node.check D_R22222 T3739 [((163/64),(163/32)),((0),(405/128)),((0),(405/128)),((163/32),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3740_ok T3759_ok
def T3738 : Node := Node.leaf L3738
theorem T3738_ok : Node.check D_R22222 T3738 [((0),(163/64)),((405/256),(405/128)),((0),(405/128)),((489/64),(163/16))] = true := Node.check_leaf_of _ _ _ L3738_ok
def T3737 : Node := Node.leaf L3737
theorem T3737_ok : Node.check D_R22222 T3737 [((0),(163/64)),((0),(405/256)),((405/256),(405/128)),((489/64),(163/16))] = true := Node.check_leaf_of _ _ _ L3737_ok
def T3736 : Node := Node.leaf L3736
theorem T3736_ok : Node.check D_R22222 T3736 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((1141/128),(163/16))] = true := Node.check_leaf_of _ _ _ L3736_ok
def T3735 : Node := Node.leaf L3735
theorem T3735_ok : Node.check D_R22222 T3735 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/256)),((489/64),(1141/128))] = true := Node.check_leaf_of _ _ _ L3735_ok
def T3734 : Node := Node.leaf L3734
theorem T3734_ok : Node.check D_R22222 T3734 [((163/128),(163/64)),((0),(405/512)),((0),(405/256)),((489/64),(1141/128))] = true := Node.check_leaf_of _ _ _ L3734_ok
def T3733 : Node := Node.split 1 T3734 T3735
theorem T3733_ok : Node.check D_R22222 T3733 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((489/64),(1141/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3734_ok T3735_ok
def T3732 : Node := Node.split 3 T3733 T3736
theorem T3732_ok : Node.check D_R22222 T3732 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((489/64),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3733_ok T3736_ok
def T3731 : Node := Node.leaf L3731
theorem T3731_ok : Node.check D_R22222 T3731 [((0),(163/128)),((405/512),(405/256)),((0),(405/256)),((1141/128),(163/16))] = true := Node.check_leaf_of _ _ _ L3731_ok
def T3730 : Node := Node.leaf L3730
theorem T3730_ok : Node.check D_R22222 T3730 [((0),(163/128)),((0),(405/512)),((0),(405/256)),((1141/128),(163/16))] = true := Node.check_leaf_of _ _ _ L3730_ok
def T3729 : Node := Node.split 1 T3730 T3731
theorem T3729_ok : Node.check D_R22222 T3729 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((1141/128),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3730_ok T3731_ok
def T3728 : Node := Node.leaf L3728
theorem T3728_ok : Node.check D_R22222 T3728 [((0),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((489/64),(1141/128))] = true := Node.check_leaf_of _ _ _ L3728_ok
def T3727 : Node := Node.leaf L3727
theorem T3727_ok : Node.check D_R22222 T3727 [((0),(163/128)),((405/512),(405/256)),((0),(405/512)),((489/64),(1141/128))] = true := Node.check_leaf_of _ _ _ L3727_ok
def T3726 : Node := Node.split 2 T3727 T3728
theorem T3726_ok : Node.check D_R22222 T3726 [((0),(163/128)),((405/512),(405/256)),((0),(405/256)),((489/64),(1141/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3727_ok T3728_ok
def T3725 : Node := Node.leaf L3725
theorem T3725_ok : Node.check D_R22222 T3725 [((0),(163/128)),((0),(405/512)),((0),(405/256)),((489/64),(1141/128))] = true := Node.check_leaf_of _ _ _ L3725_ok
def T3724 : Node := Node.split 1 T3725 T3726
theorem T3724_ok : Node.check D_R22222 T3724 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((489/64),(1141/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3725_ok T3726_ok
def T3723 : Node := Node.split 3 T3724 T3729
theorem T3723_ok : Node.check D_R22222 T3723 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((489/64),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3724_ok T3729_ok
def T3722 : Node := Node.split 0 T3723 T3732
theorem T3722_ok : Node.check D_R22222 T3722 [((0),(163/64)),((0),(405/256)),((0),(405/256)),((489/64),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3723_ok T3732_ok
def T3721 : Node := Node.split 2 T3722 T3737
theorem T3721_ok : Node.check D_R22222 T3721 [((0),(163/64)),((0),(405/256)),((0),(405/128)),((489/64),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3722_ok T3737_ok
def T3720 : Node := Node.split 1 T3721 T3738
theorem T3720_ok : Node.check D_R22222 T3720 [((0),(163/64)),((0),(405/128)),((0),(405/128)),((489/64),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3721_ok T3738_ok
def T3719 : Node := Node.leaf L3719
theorem T3719_ok : Node.check D_R22222 T3719 [((0),(163/64)),((405/256),(405/128)),((405/256),(405/128)),((163/32),(489/64))] = true := Node.check_leaf_of _ _ _ L3719_ok
def T3718 : Node := Node.leaf L3718
theorem T3718_ok : Node.check D_R22222 T3718 [((163/128),(163/64)),((405/256),(405/128)),((0),(405/256)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3718_ok
def T3717 : Node := Node.leaf L3717
theorem T3717_ok : Node.check D_R22222 T3717 [((163/128),(163/64)),((1215/512),(405/128)),((0),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3717_ok
def T3716 : Node := Node.leaf L3716
theorem T3716_ok : Node.check D_R22222 T3716 [((163/128),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3716_ok
def T3715 : Node := Node.leaf L3715
theorem T3715_ok : Node.check D_R22222 T3715 [((163/128),(163/64)),((405/256),(1215/512)),((0),(405/512)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3715_ok
def T3714 : Node := Node.split 2 T3715 T3716
theorem T3714_ok : Node.check D_R22222 T3714 [((163/128),(163/64)),((405/256),(1215/512)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3715_ok T3716_ok
def T3713 : Node := Node.split 1 T3714 T3717
theorem T3713_ok : Node.check D_R22222 T3713 [((163/128),(163/64)),((405/256),(405/128)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3714_ok T3717_ok
def T3712 : Node := Node.split 3 T3713 T3718
theorem T3712_ok : Node.check D_R22222 T3712 [((163/128),(163/64)),((405/256),(405/128)),((0),(405/256)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3713_ok T3718_ok
def T3711 : Node := Node.leaf L3711
theorem T3711_ok : Node.check D_R22222 T3711 [((0),(163/128)),((1215/512),(405/128)),((0),(405/256)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3711_ok
def T3710 : Node := Node.leaf L3710
theorem T3710_ok : Node.check D_R22222 T3710 [((0),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3710_ok
def T3709 : Node := Node.leaf L3709
theorem T3709_ok : Node.check D_R22222 T3709 [((0),(163/128)),((405/256),(1215/512)),((0),(405/512)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3709_ok
def T3708 : Node := Node.split 2 T3709 T3710
theorem T3708_ok : Node.check D_R22222 T3708 [((0),(163/128)),((405/256),(1215/512)),((0),(405/256)),((815/128),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3709_ok T3710_ok
def T3707 : Node := Node.split 1 T3708 T3711
theorem T3707_ok : Node.check D_R22222 T3707 [((0),(163/128)),((405/256),(405/128)),((0),(405/256)),((815/128),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3708_ok T3711_ok
def T3706 : Node := Node.leaf L3706
theorem T3706_ok : Node.check D_R22222 T3706 [((0),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3706_ok
def T3705 : Node := Node.leaf L3705
theorem T3705_ok : Node.check D_R22222 T3705 [((0),(163/128)),((1215/512),(405/128)),((0),(405/512)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3705_ok
def T3704 : Node := Node.split 2 T3705 T3706
theorem T3704_ok : Node.check D_R22222 T3704 [((0),(163/128)),((1215/512),(405/128)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3705_ok T3706_ok
def T3703 : Node := Node.leaf L3703
theorem T3703_ok : Node.check D_R22222 T3703 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((1467/256),(815/128))] = true := Node.check_leaf_of _ _ _ L3703_ok
def T3702 : Node := Node.leaf L3702
theorem T3702_ok : Node.check D_R22222 T3702 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/32),(1467/256))] = true := Node.check_leaf_of _ _ _ L3702_ok
def T3701 : Node := Node.leaf L3701
theorem T3701_ok : Node.check D_R22222 T3701 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(405/256)),((163/32),(1467/256))] = true := Node.check_leaf_of _ _ _ L3701_ok
def T3700 : Node := Node.split 1 T3701 T3702
theorem T3700_ok : Node.check D_R22222 T3700 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/32),(1467/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3701_ok T3702_ok
def T3699 : Node := Node.split 3 T3700 T3703
theorem T3699_ok : Node.check D_R22222 T3699 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3700_ok T3703_ok
def T3698 : Node := Node.leaf L3698
theorem T3698_ok : Node.check D_R22222 T3698 [((0),(163/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3698_ok
def T3697 : Node := Node.split 0 T3698 T3699
theorem T3697_ok : Node.check D_R22222 T3697 [((0),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3698_ok T3699_ok
def T3696 : Node := Node.leaf L3696
theorem T3696_ok : Node.check D_R22222 T3696 [((0),(163/128)),((405/256),(1215/512)),((0),(405/512)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3696_ok
def T3695 : Node := Node.split 2 T3696 T3697
theorem T3695_ok : Node.check D_R22222 T3695 [((0),(163/128)),((405/256),(1215/512)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3696_ok T3697_ok
def T3694 : Node := Node.split 1 T3695 T3704
theorem T3694_ok : Node.check D_R22222 T3694 [((0),(163/128)),((405/256),(405/128)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3695_ok T3704_ok
def T3693 : Node := Node.split 3 T3694 T3707
theorem T3693_ok : Node.check D_R22222 T3693 [((0),(163/128)),((405/256),(405/128)),((0),(405/256)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3694_ok T3707_ok
def T3692 : Node := Node.split 0 T3693 T3712
theorem T3692_ok : Node.check D_R22222 T3692 [((0),(163/64)),((405/256),(405/128)),((0),(405/256)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3693_ok T3712_ok
def T3691 : Node := Node.split 2 T3692 T3719
theorem T3691_ok : Node.check D_R22222 T3691 [((0),(163/64)),((405/256),(405/128)),((0),(405/128)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3692_ok T3719_ok
def T3690 : Node := Node.leaf L3690
theorem T3690_ok : Node.check D_R22222 T3690 [((163/128),(163/64)),((0),(405/256)),((405/256),(405/128)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3690_ok
def T3689 : Node := Node.leaf L3689
theorem T3689_ok : Node.check D_R22222 T3689 [((163/128),(163/64)),((405/512),(405/256)),((405/256),(405/128)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3689_ok
def T3688 : Node := Node.leaf L3688
theorem T3688_ok : Node.check D_R22222 T3688 [((163/128),(163/64)),((0),(405/512)),((405/256),(405/128)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3688_ok
def T3687 : Node := Node.split 1 T3688 T3689
theorem T3687_ok : Node.check D_R22222 T3687 [((163/128),(163/64)),((0),(405/256)),((405/256),(405/128)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3688_ok T3689_ok
def T3686 : Node := Node.split 3 T3687 T3690
theorem T3686_ok : Node.check D_R22222 T3686 [((163/128),(163/64)),((0),(405/256)),((405/256),(405/128)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3687_ok T3690_ok
def T3685 : Node := Node.leaf L3685
theorem T3685_ok : Node.check D_R22222 T3685 [((0),(163/128)),((405/512),(405/256)),((405/256),(405/128)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3685_ok
def T3684 : Node := Node.leaf L3684
theorem T3684_ok : Node.check D_R22222 T3684 [((0),(163/128)),((0),(405/512)),((405/256),(405/128)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3684_ok
def T3683 : Node := Node.split 1 T3684 T3685
theorem T3683_ok : Node.check D_R22222 T3683 [((0),(163/128)),((0),(405/256)),((405/256),(405/128)),((815/128),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3684_ok T3685_ok
def T3682 : Node := Node.leaf L3682
theorem T3682_ok : Node.check D_R22222 T3682 [((0),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3682_ok
def T3681 : Node := Node.leaf L3681
theorem T3681_ok : Node.check D_R22222 T3681 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((1467/256),(815/128))] = true := Node.check_leaf_of _ _ _ L3681_ok
def T3680 : Node := Node.leaf L3680
theorem T3680_ok : Node.check D_R22222 T3680 [((163/256),(163/128)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/32),(1467/256))] = true := Node.check_leaf_of _ _ _ L3680_ok
def T3679 : Node := Node.leaf L3679
theorem T3679_ok : Node.check D_R22222 T3679 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/32),(1467/256))] = true := Node.check_leaf_of _ _ _ L3679_ok
def T3678 : Node := Node.split 1 T3679 T3680
theorem T3678_ok : Node.check D_R22222 T3678 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/32),(1467/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3679_ok T3680_ok
def T3677 : Node := Node.split 3 T3678 T3681
theorem T3677_ok : Node.check D_R22222 T3677 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3678_ok T3681_ok
def T3676 : Node := Node.leaf L3676
theorem T3676_ok : Node.check D_R22222 T3676 [((0),(163/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3676_ok
def T3675 : Node := Node.split 0 T3676 T3677
theorem T3675_ok : Node.check D_R22222 T3675 [((0),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3676_ok T3677_ok
def T3674 : Node := Node.split 2 T3675 T3682
theorem T3674_ok : Node.check D_R22222 T3674 [((0),(163/128)),((405/512),(405/256)),((405/256),(405/128)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3675_ok T3682_ok
def T3673 : Node := Node.leaf L3673
theorem T3673_ok : Node.check D_R22222 T3673 [((0),(163/128)),((0),(405/512)),((405/256),(405/128)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3673_ok
def T3672 : Node := Node.split 1 T3673 T3674
theorem T3672_ok : Node.check D_R22222 T3672 [((0),(163/128)),((0),(405/256)),((405/256),(405/128)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3673_ok T3674_ok
def T3671 : Node := Node.split 3 T3672 T3683
theorem T3671_ok : Node.check D_R22222 T3671 [((0),(163/128)),((0),(405/256)),((405/256),(405/128)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3672_ok T3683_ok
def T3670 : Node := Node.split 0 T3671 T3686
theorem T3670_ok : Node.check D_R22222 T3670 [((0),(163/64)),((0),(405/256)),((405/256),(405/128)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3671_ok T3686_ok
def T3669 : Node := Node.leaf L3669
theorem T3669_ok : Node.check D_R22222 T3669 [((163/128),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3669_ok
def T3668 : Node := Node.leaf L3668
theorem T3668_ok : Node.check D_R22222 T3668 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/512)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3668_ok
def T3667 : Node := Node.split 2 T3668 T3669
theorem T3667_ok : Node.check D_R22222 T3667 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/256)),((815/128),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3668_ok T3669_ok
def T3666 : Node := Node.leaf L3666
theorem T3666_ok : Node.check D_R22222 T3666 [((163/128),(163/64)),((0),(405/512)),((0),(405/256)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3666_ok
def T3665 : Node := Node.split 1 T3666 T3667
theorem T3665_ok : Node.check D_R22222 T3665 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((815/128),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3666_ok T3667_ok
def T3664 : Node := Node.leaf L3664
theorem T3664_ok : Node.check D_R22222 T3664 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((1467/256),(815/128))] = true := Node.check_leaf_of _ _ _ L3664_ok
def T3663 : Node := Node.leaf L3663
theorem T3663_ok : Node.check D_R22222 T3663 [((489/256),(163/64)),((1215/1024),(405/256)),((405/512),(405/256)),((163/32),(1467/256))] = true := Node.check_leaf_of _ _ _ L3663_ok
def T3662 : Node := Node.leaf L3662
theorem T3662_ok : Node.check D_R22222 T3662 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/32),(1467/256))] = true := Node.check_leaf_of _ _ _ L3662_ok
def T3661 : Node := Node.leaf L3661
theorem T3661_ok : Node.check D_R22222 T3661 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/32),(1467/256))] = true := Node.check_leaf_of _ _ _ L3661_ok
def T3660 : Node := Node.split 2 T3661 T3662
theorem T3660_ok : Node.check D_R22222 T3660 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(405/256)),((163/32),(1467/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3661_ok T3662_ok
def T3659 : Node := Node.split 1 T3660 T3663
theorem T3659_ok : Node.check D_R22222 T3659 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((163/32),(1467/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3660_ok T3663_ok
def T3658 : Node := Node.split 3 T3659 T3664
theorem T3658_ok : Node.check D_R22222 T3658 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3659_ok T3664_ok
def T3657 : Node := Node.leaf L3657
theorem T3657_ok : Node.check D_R22222 T3657 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3657_ok
def T3656 : Node := Node.split 0 T3657 T3658
theorem T3656_ok : Node.check D_R22222 T3656 [((163/128),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3657_ok T3658_ok
def T3655 : Node := Node.leaf L3655
theorem T3655_ok : Node.check D_R22222 T3655 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/512)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3655_ok
def T3654 : Node := Node.split 2 T3655 T3656
theorem T3654_ok : Node.check D_R22222 T3654 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3655_ok T3656_ok
def T3653 : Node := Node.leaf L3653
theorem T3653_ok : Node.check D_R22222 T3653 [((163/128),(163/64)),((0),(405/512)),((0),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3653_ok
def T3652 : Node := Node.split 1 T3653 T3654
theorem T3652_ok : Node.check D_R22222 T3652 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3653_ok T3654_ok
def T3651 : Node := Node.split 3 T3652 T3665
theorem T3651_ok : Node.check D_R22222 T3651 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3652_ok T3665_ok
def T3650 : Node := Node.leaf L3650
theorem T3650_ok : Node.check D_R22222 T3650 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((1793/256),(489/64))] = true := Node.check_leaf_of _ _ _ L3650_ok
def T3649 : Node := Node.leaf L3649
theorem T3649_ok : Node.check D_R22222 T3649 [((163/256),(163/128)),((1215/1024),(405/256)),((405/512),(405/256)),((815/128),(1793/256))] = true := Node.check_leaf_of _ _ _ L3649_ok
def T3648 : Node := Node.leaf L3648
theorem T3648_ok : Node.check D_R22222 T3648 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(405/256)),((815/128),(1793/256))] = true := Node.check_leaf_of _ _ _ L3648_ok
def T3647 : Node := Node.split 1 T3648 T3649
theorem T3647_ok : Node.check D_R22222 T3647 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((815/128),(1793/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3648_ok T3649_ok
def T3646 : Node := Node.split 3 T3647 T3650
theorem T3646_ok : Node.check D_R22222 T3646 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((815/128),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3647_ok T3650_ok
def T3645 : Node := Node.leaf L3645
theorem T3645_ok : Node.check D_R22222 T3645 [((0),(163/256)),((405/512),(405/256)),((405/512),(405/256)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3645_ok
def T3644 : Node := Node.split 0 T3645 T3646
theorem T3644_ok : Node.check D_R22222 T3644 [((0),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((815/128),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3645_ok T3646_ok
def T3643 : Node := Node.leaf L3643
theorem T3643_ok : Node.check D_R22222 T3643 [((0),(163/128)),((405/512),(405/256)),((0),(405/512)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3643_ok
def T3642 : Node := Node.split 2 T3643 T3644
theorem T3642_ok : Node.check D_R22222 T3642 [((0),(163/128)),((405/512),(405/256)),((0),(405/256)),((815/128),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3643_ok T3644_ok
def T3641 : Node := Node.leaf L3641
theorem T3641_ok : Node.check D_R22222 T3641 [((0),(163/128)),((0),(405/512)),((0),(405/256)),((815/128),(489/64))] = true := Node.check_leaf_of _ _ _ L3641_ok
def T3640 : Node := Node.split 1 T3641 T3642
theorem T3640_ok : Node.check D_R22222 T3640 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((815/128),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3641_ok T3642_ok
def T3639 : Node := Node.leaf L3639
theorem T3639_ok : Node.check D_R22222 T3639 [((163/256),(163/128)),((1215/1024),(405/256)),((405/512),(405/256)),((1467/256),(815/128))] = true := Node.check_leaf_of _ _ _ L3639_ok
def T3638 : Node := Node.leaf L3638
theorem T3638_ok : Node.check D_R22222 T3638 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((1467/256),(815/128))] = true := Node.check_leaf_of _ _ _ L3638_ok
def T3637 : Node := Node.leaf L3637
theorem T3637_ok : Node.check D_R22222 T3637 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((3097/512),(815/128))] = true := Node.check_leaf_of _ _ _ L3637_ok
def T3636 : Node := Node.leaf L3636
theorem T3636_ok : Node.check D_R22222 T3636 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1467/256),(3097/512))] = true := Node.check_leaf_of _ _ _ L3636_ok
def T3635 : Node := Node.split 3 T3636 T3637
theorem T3635_ok : Node.check D_R22222 T3635 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1467/256),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3636_ok T3637_ok
def T3634 : Node := Node.leaf L3634
theorem T3634_ok : Node.check D_R22222 T3634 [((163/256),(489/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1467/256),(815/128))] = true := Node.check_leaf_of _ _ _ L3634_ok
def T3633 : Node := Node.split 0 T3634 T3635
theorem T3633_ok : Node.check D_R22222 T3633 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1467/256),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3634_ok T3635_ok
def T3632 : Node := Node.split 2 T3633 T3638
theorem T3632_ok : Node.check D_R22222 T3632 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(405/256)),((1467/256),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3633_ok T3638_ok
def T3631 : Node := Node.split 1 T3632 T3639
theorem T3631_ok : Node.check D_R22222 T3631 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((1467/256),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3632_ok T3639_ok
def T3630 : Node := Node.leaf L3630
theorem T3630_ok : Node.check D_R22222 T3630 [((163/256),(163/128)),((1215/1024),(405/256)),((405/512),(405/256)),((163/32),(1467/256))] = true := Node.check_leaf_of _ _ _ L3630_ok
def T3629 : Node := Node.leaf L3629
theorem T3629_ok : Node.check D_R22222 T3629 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/32),(1467/256))] = true := Node.check_leaf_of _ _ _ L3629_ok
def T3628 : Node := Node.leaf L3628
theorem T3628_ok : Node.check D_R22222 T3628 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((2771/512),(1467/256))] = true := Node.check_leaf_of _ _ _ L3628_ok
def T3627 : Node := Node.leaf L3627
theorem T3627_ok : Node.check D_R22222 T3627 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/32),(2771/512))] = true := Node.check_leaf_of _ _ _ L3627_ok
def T3626 : Node := Node.leaf L3626
theorem T3626_ok : Node.check D_R22222 T3626 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((5379/1024),(2771/512))] = true := Node.check_leaf_of _ _ _ L3626_ok
def T3625 : Node := Node.leaf L3625
theorem T3625_ok : Node.check D_R22222 T3625 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((163/32),(5379/1024))] = true := Node.check_leaf_of _ _ _ L3625_ok
def T3624 : Node := Node.leaf L3624
theorem T3624_ok : Node.check D_R22222 T3624 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((163/32),(5379/1024))] = true := Node.check_leaf_of _ _ _ L3624_ok
def T3623 : Node := Node.split 1 T3624 T3625
theorem T3623_ok : Node.check D_R22222 T3623 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/32),(5379/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3624_ok T3625_ok
def T3622 : Node := Node.split 3 T3623 T3626
theorem T3622_ok : Node.check D_R22222 T3622 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/32),(2771/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3623_ok T3626_ok
def T3621 : Node := Node.split 0 T3622 T3627
theorem T3621_ok : Node.check D_R22222 T3621 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/32),(2771/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3622_ok T3627_ok
def T3620 : Node := Node.leaf L3620
theorem T3620_ok : Node.check D_R22222 T3620 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((163/32),(2771/512))] = true := Node.check_leaf_of _ _ _ L3620_ok
def T3619 : Node := Node.split 2 T3620 T3621
theorem T3619_ok : Node.check D_R22222 T3619 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((163/32),(2771/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3620_ok T3621_ok
def T3618 : Node := Node.leaf L3618
theorem T3618_ok : Node.check D_R22222 T3618 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((163/32),(2771/512))] = true := Node.check_leaf_of _ _ _ L3618_ok
def T3617 : Node := Node.split 1 T3618 T3619
theorem T3617_ok : Node.check D_R22222 T3617 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/32),(2771/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3618_ok T3619_ok
def T3616 : Node := Node.split 3 T3617 T3628
theorem T3616_ok : Node.check D_R22222 T3616 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/32),(1467/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3617_ok T3628_ok
def T3615 : Node := Node.leaf L3615
theorem T3615_ok : Node.check D_R22222 T3615 [((163/256),(489/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/32),(1467/256))] = true := Node.check_leaf_of _ _ _ L3615_ok
def T3614 : Node := Node.split 0 T3615 T3616
theorem T3614_ok : Node.check D_R22222 T3614 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/32),(1467/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3615_ok T3616_ok
def T3613 : Node := Node.split 2 T3614 T3629
theorem T3613_ok : Node.check D_R22222 T3613 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(405/256)),((163/32),(1467/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3614_ok T3629_ok
def T3612 : Node := Node.split 1 T3613 T3630
theorem T3612_ok : Node.check D_R22222 T3612 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((163/32),(1467/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3613_ok T3630_ok
def T3611 : Node := Node.split 3 T3612 T3631
theorem T3611_ok : Node.check D_R22222 T3611 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3612_ok T3631_ok
def T3610 : Node := Node.leaf L3610
theorem T3610_ok : Node.check D_R22222 T3610 [((0),(163/256)),((405/512),(405/256)),((405/512),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3610_ok
def T3609 : Node := Node.split 0 T3610 T3611
theorem T3609_ok : Node.check D_R22222 T3609 [((0),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3610_ok T3611_ok
def T3608 : Node := Node.leaf L3608
theorem T3608_ok : Node.check D_R22222 T3608 [((0),(163/128)),((405/512),(405/256)),((0),(405/512)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3608_ok
def T3607 : Node := Node.split 2 T3608 T3609
theorem T3607_ok : Node.check D_R22222 T3607 [((0),(163/128)),((405/512),(405/256)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3608_ok T3609_ok
def T3606 : Node := Node.leaf L3606
theorem T3606_ok : Node.check D_R22222 T3606 [((0),(163/128)),((0),(405/512)),((0),(405/256)),((163/32),(815/128))] = true := Node.check_leaf_of _ _ _ L3606_ok
def T3605 : Node := Node.split 1 T3606 T3607
theorem T3605_ok : Node.check D_R22222 T3605 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((163/32),(815/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3606_ok T3607_ok
def T3604 : Node := Node.split 3 T3605 T3640
theorem T3604_ok : Node.check D_R22222 T3604 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3605_ok T3640_ok
def T3603 : Node := Node.split 0 T3604 T3651
theorem T3603_ok : Node.check D_R22222 T3603 [((0),(163/64)),((0),(405/256)),((0),(405/256)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3604_ok T3651_ok
def T3602 : Node := Node.split 2 T3603 T3670
theorem T3602_ok : Node.check D_R22222 T3602 [((0),(163/64)),((0),(405/256)),((0),(405/128)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3603_ok T3670_ok
def T3601 : Node := Node.split 1 T3602 T3691
theorem T3601_ok : Node.check D_R22222 T3601 [((0),(163/64)),((0),(405/128)),((0),(405/128)),((163/32),(489/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3602_ok T3691_ok
def T3600 : Node := Node.split 3 T3601 T3720
theorem T3600_ok : Node.check D_R22222 T3600 [((0),(163/64)),((0),(405/128)),((0),(405/128)),((163/32),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3601_ok T3720_ok
def T3599 : Node := Node.split 0 T3600 T3739
theorem T3599_ok : Node.check D_R22222 T3599 [((0),(163/32)),((0),(405/128)),((0),(405/128)),((163/32),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3600_ok T3739_ok
def T3598 : Node := Node.split 2 T3599 T3760
theorem T3598_ok : Node.check D_R22222 T3598 [((0),(163/32)),((0),(405/128)),((0),(405/64)),((163/32),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3599_ok T3760_ok
def T3597 : Node := Node.split 1 T3598 T3761
theorem T3597_ok : Node.check D_R22222 T3597 [((0),(163/32)),((0),(405/64)),((0),(405/64)),((163/32),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3598_ok T3761_ok
def T3596 : Node := Node.leaf L3596
theorem T3596_ok : Node.check D_R22222 T3596 [((0),(163/32)),((405/128),(405/64)),((405/128),(405/64)),((0),(163/32))] = true := Node.check_leaf_of _ _ _ L3596_ok
def T3595 : Node := Node.leaf L3595
theorem T3595_ok : Node.check D_R22222 T3595 [((163/64),(163/32)),((405/128),(405/64)),((0),(405/128)),((163/64),(163/32))] = true := Node.check_leaf_of _ _ _ L3595_ok
def T3594 : Node := Node.leaf L3594
theorem T3594_ok : Node.check D_R22222 T3594 [((163/64),(163/32)),((1215/256),(405/64)),((0),(405/128)),((0),(163/64))] = true := Node.check_leaf_of _ _ _ L3594_ok
def T3593 : Node := Node.leaf L3593
theorem T3593_ok : Node.check D_R22222 T3593 [((163/64),(163/32)),((405/128),(1215/256)),((405/256),(405/128)),((0),(163/64))] = true := Node.check_leaf_of _ _ _ L3593_ok
def T3592 : Node := Node.leaf L3592
theorem T3592_ok : Node.check D_R22222 T3592 [((489/128),(163/32)),((405/128),(1215/256)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3592_ok
def T3591 : Node := Node.leaf L3591
theorem T3591_ok : Node.check D_R22222 T3591 [((489/128),(163/32)),((2025/512),(1215/256)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3591_ok
def T3590 : Node := Node.leaf L3590
theorem T3590_ok : Node.check D_R22222 T3590 [((489/128),(163/32)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3590_ok
def T3589 : Node := Node.leaf L3589
theorem T3589_ok : Node.check D_R22222 T3589 [((489/128),(163/32)),((405/128),(2025/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3589_ok
def T3588 : Node := Node.split 2 T3589 T3590
theorem T3588_ok : Node.check D_R22222 T3588 [((489/128),(163/32)),((405/128),(2025/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3589_ok T3590_ok
def T3587 : Node := Node.split 1 T3588 T3591
theorem T3587_ok : Node.check D_R22222 T3587 [((489/128),(163/32)),((405/128),(1215/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3588_ok T3591_ok
def T3586 : Node := Node.split 3 T3587 T3592
theorem T3586_ok : Node.check D_R22222 T3586 [((489/128),(163/32)),((405/128),(1215/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3587_ok T3592_ok
def T3585 : Node := Node.leaf L3585
theorem T3585_ok : Node.check D_R22222 T3585 [((163/64),(489/128)),((2025/512),(1215/256)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3585_ok
def T3584 : Node := Node.leaf L3584
theorem T3584_ok : Node.check D_R22222 T3584 [((163/64),(489/128)),((405/128),(2025/512)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3584_ok
def T3583 : Node := Node.leaf L3583
theorem T3583_ok : Node.check D_R22222 T3583 [((163/64),(489/128)),((405/128),(2025/512)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3583_ok
def T3582 : Node := Node.split 2 T3583 T3584
theorem T3582_ok : Node.check D_R22222 T3582 [((163/64),(489/128)),((405/128),(2025/512)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3583_ok T3584_ok
def T3581 : Node := Node.split 1 T3582 T3585
theorem T3581_ok : Node.check D_R22222 T3581 [((163/64),(489/128)),((405/128),(1215/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3582_ok T3585_ok
def T3580 : Node := Node.leaf L3580
theorem T3580_ok : Node.check D_R22222 T3580 [((163/64),(489/128)),((2025/512),(1215/256)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3580_ok
def T3579 : Node := Node.leaf L3579
theorem T3579_ok : Node.check D_R22222 T3579 [((163/64),(489/128)),((2025/512),(1215/256)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3579_ok
def T3578 : Node := Node.split 2 T3579 T3580
theorem T3578_ok : Node.check D_R22222 T3578 [((163/64),(489/128)),((2025/512),(1215/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3579_ok T3580_ok
def T3577 : Node := Node.leaf L3577
theorem T3577_ok : Node.check D_R22222 T3577 [((815/256),(489/128)),((405/128),(2025/512)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3577_ok
def T3576 : Node := Node.leaf L3576
theorem T3576_ok : Node.check D_R22222 T3576 [((815/256),(489/128)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3576_ok
def T3575 : Node := Node.split 3 T3576 T3577
theorem T3575_ok : Node.check D_R22222 T3575 [((815/256),(489/128)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3576_ok T3577_ok
def T3574 : Node := Node.leaf L3574
theorem T3574_ok : Node.check D_R22222 T3574 [((163/64),(815/256)),((405/128),(2025/512)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3574_ok
def T3573 : Node := Node.leaf L3573
theorem T3573_ok : Node.check D_R22222 T3573 [((163/64),(815/256)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3573_ok
def T3572 : Node := Node.split 3 T3573 T3574
theorem T3572_ok : Node.check D_R22222 T3572 [((163/64),(815/256)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3573_ok T3574_ok
def T3571 : Node := Node.split 0 T3572 T3575
theorem T3571_ok : Node.check D_R22222 T3571 [((163/64),(489/128)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3572_ok T3575_ok
def T3570 : Node := Node.leaf L3570
theorem T3570_ok : Node.check D_R22222 T3570 [((163/64),(489/128)),((405/128),(2025/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3570_ok
def T3569 : Node := Node.split 2 T3570 T3571
theorem T3569_ok : Node.check D_R22222 T3569 [((163/64),(489/128)),((405/128),(2025/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3570_ok T3571_ok
def T3568 : Node := Node.split 1 T3569 T3578
theorem T3568_ok : Node.check D_R22222 T3568 [((163/64),(489/128)),((405/128),(1215/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3569_ok T3578_ok
def T3567 : Node := Node.split 3 T3568 T3581
theorem T3567_ok : Node.check D_R22222 T3567 [((163/64),(489/128)),((405/128),(1215/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3568_ok T3581_ok
def T3566 : Node := Node.split 0 T3567 T3586
theorem T3566_ok : Node.check D_R22222 T3566 [((163/64),(163/32)),((405/128),(1215/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3567_ok T3586_ok
def T3565 : Node := Node.split 2 T3566 T3593
theorem T3565_ok : Node.check D_R22222 T3565 [((163/64),(163/32)),((405/128),(1215/256)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3566_ok T3593_ok
def T3564 : Node := Node.split 1 T3565 T3594
theorem T3564_ok : Node.check D_R22222 T3564 [((163/64),(163/32)),((405/128),(405/64)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3565_ok T3594_ok
def T3563 : Node := Node.split 3 T3564 T3595
theorem T3563_ok : Node.check D_R22222 T3563 [((163/64),(163/32)),((405/128),(405/64)),((0),(405/128)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3564_ok T3595_ok
def T3562 : Node := Node.leaf L3562
theorem T3562_ok : Node.check D_R22222 T3562 [((0),(163/64)),((1215/256),(405/64)),((0),(405/128)),((163/64),(163/32))] = true := Node.check_leaf_of _ _ _ L3562_ok
def T3561 : Node := Node.leaf L3561
theorem T3561_ok : Node.check D_R22222 T3561 [((0),(163/64)),((405/128),(1215/256)),((405/256),(405/128)),((163/64),(163/32))] = true := Node.check_leaf_of _ _ _ L3561_ok
def T3560 : Node := Node.leaf L3560
theorem T3560_ok : Node.check D_R22222 T3560 [((163/128),(163/64)),((405/128),(1215/256)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3560_ok
def T3559 : Node := Node.leaf L3559
theorem T3559_ok : Node.check D_R22222 T3559 [((163/128),(163/64)),((2025/512),(1215/256)),((0),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3559_ok
def T3558 : Node := Node.leaf L3558
theorem T3558_ok : Node.check D_R22222 T3558 [((163/128),(163/64)),((405/128),(2025/512)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3558_ok
def T3557 : Node := Node.leaf L3557
theorem T3557_ok : Node.check D_R22222 T3557 [((163/128),(163/64)),((405/128),(2025/512)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3557_ok
def T3556 : Node := Node.split 2 T3557 T3558
theorem T3556_ok : Node.check D_R22222 T3556 [((163/128),(163/64)),((405/128),(2025/512)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3557_ok T3558_ok
def T3555 : Node := Node.split 1 T3556 T3559
theorem T3555_ok : Node.check D_R22222 T3555 [((163/128),(163/64)),((405/128),(1215/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3556_ok T3559_ok
def T3554 : Node := Node.split 3 T3555 T3560
theorem T3554_ok : Node.check D_R22222 T3554 [((163/128),(163/64)),((405/128),(1215/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3555_ok T3560_ok
def T3553 : Node := Node.leaf L3553
theorem T3553_ok : Node.check D_R22222 T3553 [((0),(163/128)),((2025/512),(1215/256)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3553_ok
def T3552 : Node := Node.leaf L3552
theorem T3552_ok : Node.check D_R22222 T3552 [((0),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3552_ok
def T3551 : Node := Node.leaf L3551
theorem T3551_ok : Node.check D_R22222 T3551 [((0),(163/128)),((405/128),(2025/512)),((0),(405/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3551_ok
def T3550 : Node := Node.split 2 T3551 T3552
theorem T3550_ok : Node.check D_R22222 T3550 [((0),(163/128)),((405/128),(2025/512)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3551_ok T3552_ok
def T3549 : Node := Node.split 1 T3550 T3553
theorem T3549_ok : Node.check D_R22222 T3549 [((0),(163/128)),((405/128),(1215/256)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3550_ok T3553_ok
def T3548 : Node := Node.leaf L3548
theorem T3548_ok : Node.check D_R22222 T3548 [((0),(163/128)),((2025/512),(1215/256)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3548_ok
def T3547 : Node := Node.leaf L3547
theorem T3547_ok : Node.check D_R22222 T3547 [((0),(163/128)),((2025/512),(1215/256)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3547_ok
def T3546 : Node := Node.split 2 T3547 T3548
theorem T3546_ok : Node.check D_R22222 T3546 [((0),(163/128)),((2025/512),(1215/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3547_ok T3548_ok
def T3545 : Node := Node.leaf L3545
theorem T3545_ok : Node.check D_R22222 T3545 [((163/256),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L3545_ok
def T3544 : Node := Node.leaf L3544
theorem T3544_ok : Node.check D_R22222 T3544 [((163/256),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3544_ok
def T3543 : Node := Node.split 3 T3544 T3545
theorem T3543_ok : Node.check D_R22222 T3543 [((163/256),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3544_ok T3545_ok
def T3542 : Node := Node.leaf L3542
theorem T3542_ok : Node.check D_R22222 T3542 [((0),(163/256)),((405/128),(2025/512)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3542_ok
def T3541 : Node := Node.split 0 T3542 T3543
theorem T3541_ok : Node.check D_R22222 T3541 [((0),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3542_ok T3543_ok
def T3540 : Node := Node.leaf L3540
theorem T3540_ok : Node.check D_R22222 T3540 [((0),(163/128)),((405/128),(2025/512)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3540_ok
def T3539 : Node := Node.split 2 T3540 T3541
theorem T3539_ok : Node.check D_R22222 T3539 [((0),(163/128)),((405/128),(2025/512)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3540_ok T3541_ok
def T3538 : Node := Node.split 1 T3539 T3546
theorem T3538_ok : Node.check D_R22222 T3538 [((0),(163/128)),((405/128),(1215/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3539_ok T3546_ok
def T3537 : Node := Node.split 3 T3538 T3549
theorem T3537_ok : Node.check D_R22222 T3537 [((0),(163/128)),((405/128),(1215/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3538_ok T3549_ok
def T3536 : Node := Node.split 0 T3537 T3554
theorem T3536_ok : Node.check D_R22222 T3536 [((0),(163/64)),((405/128),(1215/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3537_ok T3554_ok
def T3535 : Node := Node.split 2 T3536 T3561
theorem T3535_ok : Node.check D_R22222 T3535 [((0),(163/64)),((405/128),(1215/256)),((0),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3536_ok T3561_ok
def T3534 : Node := Node.split 1 T3535 T3562
theorem T3534_ok : Node.check D_R22222 T3534 [((0),(163/64)),((405/128),(405/64)),((0),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3535_ok T3562_ok
def T3533 : Node := Node.leaf L3533
theorem T3533_ok : Node.check D_R22222 T3533 [((0),(163/64)),((1215/256),(405/64)),((405/256),(405/128)),((0),(163/64))] = true := Node.check_leaf_of _ _ _ L3533_ok
def T3532 : Node := Node.leaf L3532
theorem T3532_ok : Node.check D_R22222 T3532 [((163/128),(163/64)),((1215/256),(405/64)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3532_ok
def T3531 : Node := Node.leaf L3531
theorem T3531_ok : Node.check D_R22222 T3531 [((163/128),(163/64)),((2835/512),(405/64)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3531_ok
def T3530 : Node := Node.leaf L3530
theorem T3530_ok : Node.check D_R22222 T3530 [((163/128),(163/64)),((1215/256),(2835/512)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3530_ok
def T3529 : Node := Node.leaf L3529
theorem T3529_ok : Node.check D_R22222 T3529 [((163/128),(163/64)),((1215/256),(2835/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3529_ok
def T3528 : Node := Node.split 2 T3529 T3530
theorem T3528_ok : Node.check D_R22222 T3528 [((163/128),(163/64)),((1215/256),(2835/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3529_ok T3530_ok
def T3527 : Node := Node.split 1 T3528 T3531
theorem T3527_ok : Node.check D_R22222 T3527 [((163/128),(163/64)),((1215/256),(405/64)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3528_ok T3531_ok
def T3526 : Node := Node.split 3 T3527 T3532
theorem T3526_ok : Node.check D_R22222 T3526 [((163/128),(163/64)),((1215/256),(405/64)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3527_ok T3532_ok
def T3525 : Node := Node.leaf L3525
theorem T3525_ok : Node.check D_R22222 T3525 [((0),(163/128)),((2835/512),(405/64)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3525_ok
def T3524 : Node := Node.leaf L3524
theorem T3524_ok : Node.check D_R22222 T3524 [((0),(163/128)),((1215/256),(2835/512)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3524_ok
def T3523 : Node := Node.leaf L3523
theorem T3523_ok : Node.check D_R22222 T3523 [((0),(163/128)),((1215/256),(2835/512)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3523_ok
def T3522 : Node := Node.split 2 T3523 T3524
theorem T3522_ok : Node.check D_R22222 T3522 [((0),(163/128)),((1215/256),(2835/512)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3523_ok T3524_ok
def T3521 : Node := Node.split 1 T3522 T3525
theorem T3521_ok : Node.check D_R22222 T3521 [((0),(163/128)),((1215/256),(405/64)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3522_ok T3525_ok
def T3520 : Node := Node.leaf L3520
theorem T3520_ok : Node.check D_R22222 T3520 [((0),(163/128)),((2835/512),(405/64)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3520_ok
def T3519 : Node := Node.leaf L3519
theorem T3519_ok : Node.check D_R22222 T3519 [((163/256),(163/128)),((2835/512),(405/64)),((0),(405/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3519_ok
def T3518 : Node := Node.leaf L3518
theorem T3518_ok : Node.check D_R22222 T3518 [((163/256),(163/128)),((2835/512),(405/64)),((0),(405/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3518_ok
def T3517 : Node := Node.split 3 T3518 T3519
theorem T3517_ok : Node.check D_R22222 T3517 [((163/256),(163/128)),((2835/512),(405/64)),((0),(405/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3518_ok T3519_ok
def T3516 : Node := Node.leaf L3516
theorem T3516_ok : Node.check D_R22222 T3516 [((0),(163/256)),((2835/512),(405/64)),((0),(405/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3516_ok
def T3515 : Node := Node.leaf L3515
theorem T3515_ok : Node.check D_R22222 T3515 [((0),(163/256)),((2835/512),(405/64)),((0),(405/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3515_ok
def T3514 : Node := Node.split 3 T3515 T3516
theorem T3514_ok : Node.check D_R22222 T3514 [((0),(163/256)),((2835/512),(405/64)),((0),(405/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3515_ok T3516_ok
def T3513 : Node := Node.split 0 T3514 T3517
theorem T3513_ok : Node.check D_R22222 T3513 [((0),(163/128)),((2835/512),(405/64)),((0),(405/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3514_ok T3517_ok
def T3512 : Node := Node.split 2 T3513 T3520
theorem T3512_ok : Node.check D_R22222 T3512 [((0),(163/128)),((2835/512),(405/64)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3513_ok T3520_ok
def T3511 : Node := Node.leaf L3511
theorem T3511_ok : Node.check D_R22222 T3511 [((163/256),(163/128)),((1215/256),(2835/512)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3511_ok
def T3510 : Node := Node.leaf L3510
theorem T3510_ok : Node.check D_R22222 T3510 [((163/256),(163/128)),((1215/256),(2835/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3510_ok
def T3509 : Node := Node.split 3 T3510 T3511
theorem T3509_ok : Node.check D_R22222 T3509 [((163/256),(163/128)),((1215/256),(2835/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3510_ok T3511_ok
def T3508 : Node := Node.leaf L3508
theorem T3508_ok : Node.check D_R22222 T3508 [((0),(163/256)),((1215/256),(2835/512)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3508_ok
def T3507 : Node := Node.split 0 T3508 T3509
theorem T3507_ok : Node.check D_R22222 T3507 [((0),(163/128)),((1215/256),(2835/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3508_ok T3509_ok
def T3506 : Node := Node.leaf L3506
theorem T3506_ok : Node.check D_R22222 T3506 [((0),(163/128)),((1215/256),(2835/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3506_ok
def T3505 : Node := Node.split 2 T3506 T3507
theorem T3505_ok : Node.check D_R22222 T3505 [((0),(163/128)),((1215/256),(2835/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3506_ok T3507_ok
def T3504 : Node := Node.split 1 T3505 T3512
theorem T3504_ok : Node.check D_R22222 T3504 [((0),(163/128)),((1215/256),(405/64)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3505_ok T3512_ok
def T3503 : Node := Node.split 3 T3504 T3521
theorem T3503_ok : Node.check D_R22222 T3503 [((0),(163/128)),((1215/256),(405/64)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3504_ok T3521_ok
def T3502 : Node := Node.split 0 T3503 T3526
theorem T3502_ok : Node.check D_R22222 T3502 [((0),(163/64)),((1215/256),(405/64)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3503_ok T3526_ok
def T3501 : Node := Node.split 2 T3502 T3533
theorem T3501_ok : Node.check D_R22222 T3501 [((0),(163/64)),((1215/256),(405/64)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3502_ok T3533_ok
def T3500 : Node := Node.leaf L3500
theorem T3500_ok : Node.check D_R22222 T3500 [((163/128),(163/64)),((405/128),(1215/256)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3500_ok
def T3499 : Node := Node.leaf L3499
theorem T3499_ok : Node.check D_R22222 T3499 [((163/128),(163/64)),((2025/512),(1215/256)),((405/256),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3499_ok
def T3498 : Node := Node.leaf L3498
theorem T3498_ok : Node.check D_R22222 T3498 [((163/128),(163/64)),((405/128),(2025/512)),((1215/512),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3498_ok
def T3497 : Node := Node.leaf L3497
theorem T3497_ok : Node.check D_R22222 T3497 [((489/256),(163/64)),((405/128),(2025/512)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3497_ok
def T3496 : Node := Node.leaf L3496
theorem T3496_ok : Node.check D_R22222 T3496 [((489/256),(163/64)),((405/128),(2025/512)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3496_ok
def T3495 : Node := Node.split 3 T3496 T3497
theorem T3495_ok : Node.check D_R22222 T3495 [((489/256),(163/64)),((405/128),(2025/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3496_ok T3497_ok
def T3494 : Node := Node.leaf L3494
theorem T3494_ok : Node.check D_R22222 T3494 [((163/128),(489/256)),((405/128),(2025/512)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3494_ok
def T3493 : Node := Node.leaf L3493
theorem T3493_ok : Node.check D_R22222 T3493 [((163/128),(489/256)),((405/128),(2025/512)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3493_ok
def T3492 : Node := Node.split 3 T3493 T3494
theorem T3492_ok : Node.check D_R22222 T3492 [((163/128),(489/256)),((405/128),(2025/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3493_ok T3494_ok
def T3491 : Node := Node.split 0 T3492 T3495
theorem T3491_ok : Node.check D_R22222 T3491 [((163/128),(163/64)),((405/128),(2025/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3492_ok T3495_ok
def T3490 : Node := Node.split 2 T3491 T3498
theorem T3490_ok : Node.check D_R22222 T3490 [((163/128),(163/64)),((405/128),(2025/512)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3491_ok T3498_ok
def T3489 : Node := Node.split 1 T3490 T3499
theorem T3489_ok : Node.check D_R22222 T3489 [((163/128),(163/64)),((405/128),(1215/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3490_ok T3499_ok
def T3488 : Node := Node.split 3 T3489 T3500
theorem T3488_ok : Node.check D_R22222 T3488 [((163/128),(163/64)),((405/128),(1215/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3489_ok T3500_ok
def T3487 : Node := Node.leaf L3487
theorem T3487_ok : Node.check D_R22222 T3487 [((0),(163/128)),((2025/512),(1215/256)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3487_ok
def T3486 : Node := Node.leaf L3486
theorem T3486_ok : Node.check D_R22222 T3486 [((0),(163/128)),((405/128),(2025/512)),((1215/512),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3486_ok
def T3485 : Node := Node.leaf L3485
theorem T3485_ok : Node.check D_R22222 T3485 [((163/256),(163/128)),((405/128),(2025/512)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3485_ok
def T3484 : Node := Node.leaf L3484
theorem T3484_ok : Node.check D_R22222 T3484 [((163/256),(163/128)),((405/128),(2025/512)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L3484_ok
def T3483 : Node := Node.split 3 T3484 T3485
theorem T3483_ok : Node.check D_R22222 T3483 [((163/256),(163/128)),((405/128),(2025/512)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3484_ok T3485_ok
def T3482 : Node := Node.leaf L3482
theorem T3482_ok : Node.check D_R22222 T3482 [((0),(163/256)),((405/128),(2025/512)),((405/256),(1215/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3482_ok
def T3481 : Node := Node.split 0 T3482 T3483
theorem T3481_ok : Node.check D_R22222 T3481 [((0),(163/128)),((405/128),(2025/512)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3482_ok T3483_ok
def T3480 : Node := Node.split 2 T3481 T3486
theorem T3480_ok : Node.check D_R22222 T3480 [((0),(163/128)),((405/128),(2025/512)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3481_ok T3486_ok
def T3479 : Node := Node.split 1 T3480 T3487
theorem T3479_ok : Node.check D_R22222 T3479 [((0),(163/128)),((405/128),(1215/256)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3480_ok T3487_ok
def T3478 : Node := Node.leaf L3478
theorem T3478_ok : Node.check D_R22222 T3478 [((0),(163/128)),((2025/512),(1215/256)),((1215/512),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3478_ok
def T3477 : Node := Node.leaf L3477
theorem T3477_ok : Node.check D_R22222 T3477 [((163/256),(163/128)),((2025/512),(1215/256)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3477_ok
def T3476 : Node := Node.leaf L3476
theorem T3476_ok : Node.check D_R22222 T3476 [((163/256),(163/128)),((2025/512),(1215/256)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3476_ok
def T3475 : Node := Node.split 3 T3476 T3477
theorem T3475_ok : Node.check D_R22222 T3475 [((163/256),(163/128)),((2025/512),(1215/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3476_ok T3477_ok
def T3474 : Node := Node.leaf L3474
theorem T3474_ok : Node.check D_R22222 T3474 [((0),(163/256)),((2025/512),(1215/256)),((405/256),(1215/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3474_ok
def T3473 : Node := Node.split 0 T3474 T3475
theorem T3473_ok : Node.check D_R22222 T3473 [((0),(163/128)),((2025/512),(1215/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3474_ok T3475_ok
def T3472 : Node := Node.split 2 T3473 T3478
theorem T3472_ok : Node.check D_R22222 T3472 [((0),(163/128)),((2025/512),(1215/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3473_ok T3478_ok
def T3471 : Node := Node.leaf L3471
theorem T3471_ok : Node.check D_R22222 T3471 [((163/256),(163/128)),((405/128),(2025/512)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3471_ok
def T3470 : Node := Node.leaf L3470
theorem T3470_ok : Node.check D_R22222 T3470 [((163/256),(163/128)),((405/128),(2025/512)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3470_ok
def T3469 : Node := Node.split 3 T3470 T3471
theorem T3469_ok : Node.check D_R22222 T3469 [((163/256),(163/128)),((405/128),(2025/512)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3470_ok T3471_ok
def T3468 : Node := Node.leaf L3468
theorem T3468_ok : Node.check D_R22222 T3468 [((0),(163/256)),((405/128),(2025/512)),((1215/512),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3468_ok
def T3467 : Node := Node.split 0 T3468 T3469
theorem T3467_ok : Node.check D_R22222 T3467 [((0),(163/128)),((405/128),(2025/512)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3468_ok T3469_ok
def T3466 : Node := Node.leaf L3466
theorem T3466_ok : Node.check D_R22222 T3466 [((163/256),(163/128)),((3645/1024),(2025/512)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3466_ok
def T3465 : Node := Node.leaf L3465
theorem T3465_ok : Node.check D_R22222 T3465 [((163/256),(163/128)),((405/128),(3645/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3465_ok
def T3464 : Node := Node.split 1 T3465 T3466
theorem T3464_ok : Node.check D_R22222 T3464 [((163/256),(163/128)),((405/128),(2025/512)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3465_ok T3466_ok
def T3463 : Node := Node.leaf L3463
theorem T3463_ok : Node.check D_R22222 T3463 [((163/256),(163/128)),((405/128),(2025/512)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3463_ok
def T3462 : Node := Node.split 3 T3463 T3464
theorem T3462_ok : Node.check D_R22222 T3462 [((163/256),(163/128)),((405/128),(2025/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3463_ok T3464_ok
def T3461 : Node := Node.leaf L3461
theorem T3461_ok : Node.check D_R22222 T3461 [((0),(163/256)),((405/128),(2025/512)),((405/256),(1215/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3461_ok
def T3460 : Node := Node.split 0 T3461 T3462
theorem T3460_ok : Node.check D_R22222 T3460 [((0),(163/128)),((405/128),(2025/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3461_ok T3462_ok
def T3459 : Node := Node.split 2 T3460 T3467
theorem T3459_ok : Node.check D_R22222 T3459 [((0),(163/128)),((405/128),(2025/512)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3460_ok T3467_ok
def T3458 : Node := Node.split 1 T3459 T3472
theorem T3458_ok : Node.check D_R22222 T3458 [((0),(163/128)),((405/128),(1215/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3459_ok T3472_ok
def T3457 : Node := Node.split 3 T3458 T3479
theorem T3457_ok : Node.check D_R22222 T3457 [((0),(163/128)),((405/128),(1215/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3458_ok T3479_ok
def T3456 : Node := Node.split 0 T3457 T3488
theorem T3456_ok : Node.check D_R22222 T3456 [((0),(163/64)),((405/128),(1215/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3457_ok T3488_ok
def T3455 : Node := Node.leaf L3455
theorem T3455_ok : Node.check D_R22222 T3455 [((163/128),(163/64)),((2025/512),(1215/256)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3455_ok
def T3454 : Node := Node.leaf L3454
theorem T3454_ok : Node.check D_R22222 T3454 [((163/128),(163/64)),((2025/512),(1215/256)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3454_ok
def T3453 : Node := Node.split 2 T3454 T3455
theorem T3453_ok : Node.check D_R22222 T3453 [((163/128),(163/64)),((2025/512),(1215/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3454_ok T3455_ok
def T3452 : Node := Node.leaf L3452
theorem T3452_ok : Node.check D_R22222 T3452 [((489/256),(163/64)),((405/128),(2025/512)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3452_ok
def T3451 : Node := Node.leaf L3451
theorem T3451_ok : Node.check D_R22222 T3451 [((489/256),(163/64)),((405/128),(2025/512)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L3451_ok
def T3450 : Node := Node.split 3 T3451 T3452
theorem T3450_ok : Node.check D_R22222 T3450 [((489/256),(163/64)),((405/128),(2025/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3451_ok T3452_ok
def T3449 : Node := Node.leaf L3449
theorem T3449_ok : Node.check D_R22222 T3449 [((163/128),(489/256)),((405/128),(2025/512)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3449_ok
def T3448 : Node := Node.split 0 T3449 T3450
theorem T3448_ok : Node.check D_R22222 T3448 [((163/128),(163/64)),((405/128),(2025/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3449_ok T3450_ok
def T3447 : Node := Node.leaf L3447
theorem T3447_ok : Node.check D_R22222 T3447 [((163/128),(163/64)),((405/128),(2025/512)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3447_ok
def T3446 : Node := Node.split 2 T3447 T3448
theorem T3446_ok : Node.check D_R22222 T3446 [((163/128),(163/64)),((405/128),(2025/512)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3447_ok T3448_ok
def T3445 : Node := Node.split 1 T3446 T3453
theorem T3445_ok : Node.check D_R22222 T3445 [((163/128),(163/64)),((405/128),(1215/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3446_ok T3453_ok
def T3444 : Node := Node.leaf L3444
theorem T3444_ok : Node.check D_R22222 T3444 [((489/256),(163/64)),((2025/512),(1215/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3444_ok
def T3443 : Node := Node.leaf L3443
theorem T3443_ok : Node.check D_R22222 T3443 [((489/256),(163/64)),((2025/512),(1215/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3443_ok
def T3442 : Node := Node.split 3 T3443 T3444
theorem T3442_ok : Node.check D_R22222 T3442 [((489/256),(163/64)),((2025/512),(1215/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3443_ok T3444_ok
def T3441 : Node := Node.leaf L3441
theorem T3441_ok : Node.check D_R22222 T3441 [((163/128),(489/256)),((2025/512),(1215/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3441_ok
def T3440 : Node := Node.leaf L3440
theorem T3440_ok : Node.check D_R22222 T3440 [((163/128),(489/256)),((2025/512),(1215/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3440_ok
def T3439 : Node := Node.split 3 T3440 T3441
theorem T3439_ok : Node.check D_R22222 T3439 [((163/128),(489/256)),((2025/512),(1215/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3440_ok T3441_ok
def T3438 : Node := Node.split 0 T3439 T3442
theorem T3438_ok : Node.check D_R22222 T3438 [((163/128),(163/64)),((2025/512),(1215/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3439_ok T3442_ok
def T3437 : Node := Node.leaf L3437
theorem T3437_ok : Node.check D_R22222 T3437 [((163/128),(163/64)),((2025/512),(1215/256)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3437_ok
def T3436 : Node := Node.split 2 T3437 T3438
theorem T3436_ok : Node.check D_R22222 T3436 [((163/128),(163/64)),((2025/512),(1215/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3437_ok T3438_ok
def T3435 : Node := Node.leaf L3435
theorem T3435_ok : Node.check D_R22222 T3435 [((489/256),(163/64)),((3645/1024),(2025/512)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3435_ok
def T3434 : Node := Node.leaf L3434
theorem T3434_ok : Node.check D_R22222 T3434 [((489/256),(163/64)),((405/128),(3645/1024)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3434_ok
def T3433 : Node := Node.split 1 T3434 T3435
theorem T3433_ok : Node.check D_R22222 T3433 [((489/256),(163/64)),((405/128),(2025/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3434_ok T3435_ok
def T3432 : Node := Node.leaf L3432
theorem T3432_ok : Node.check D_R22222 T3432 [((489/256),(163/64)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3432_ok
def T3431 : Node := Node.split 3 T3432 T3433
theorem T3431_ok : Node.check D_R22222 T3431 [((489/256),(163/64)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3432_ok T3433_ok
def T3430 : Node := Node.leaf L3430
theorem T3430_ok : Node.check D_R22222 T3430 [((163/128),(489/256)),((405/128),(2025/512)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3430_ok
def T3429 : Node := Node.leaf L3429
theorem T3429_ok : Node.check D_R22222 T3429 [((163/128),(489/256)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3429_ok
def T3428 : Node := Node.split 3 T3429 T3430
theorem T3428_ok : Node.check D_R22222 T3428 [((163/128),(489/256)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3429_ok T3430_ok
def T3427 : Node := Node.split 0 T3428 T3431
theorem T3427_ok : Node.check D_R22222 T3427 [((163/128),(163/64)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3428_ok T3431_ok
def T3426 : Node := Node.leaf L3426
theorem T3426_ok : Node.check D_R22222 T3426 [((163/128),(163/64)),((405/128),(2025/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3426_ok
def T3425 : Node := Node.split 2 T3426 T3427
theorem T3425_ok : Node.check D_R22222 T3425 [((163/128),(163/64)),((405/128),(2025/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3426_ok T3427_ok
def T3424 : Node := Node.split 1 T3425 T3436
theorem T3424_ok : Node.check D_R22222 T3424 [((163/128),(163/64)),((405/128),(1215/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3425_ok T3436_ok
def T3423 : Node := Node.split 3 T3424 T3445
theorem T3423_ok : Node.check D_R22222 T3423 [((163/128),(163/64)),((405/128),(1215/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3424_ok T3445_ok
def T3422 : Node := Node.leaf L3422
theorem T3422_ok : Node.check D_R22222 T3422 [((163/256),(163/128)),((2025/512),(1215/256)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3422_ok
def T3421 : Node := Node.leaf L3421
theorem T3421_ok : Node.check D_R22222 T3421 [((163/256),(163/128)),((2025/512),(1215/256)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L3421_ok
def T3420 : Node := Node.split 3 T3421 T3422
theorem T3420_ok : Node.check D_R22222 T3420 [((163/256),(163/128)),((2025/512),(1215/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3421_ok T3422_ok
def T3419 : Node := Node.leaf L3419
theorem T3419_ok : Node.check D_R22222 T3419 [((0),(163/256)),((2025/512),(1215/256)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3419_ok
def T3418 : Node := Node.split 0 T3419 T3420
theorem T3418_ok : Node.check D_R22222 T3418 [((0),(163/128)),((2025/512),(1215/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3419_ok T3420_ok
def T3417 : Node := Node.leaf L3417
theorem T3417_ok : Node.check D_R22222 T3417 [((0),(163/128)),((2025/512),(1215/256)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3417_ok
def T3416 : Node := Node.split 2 T3417 T3418
theorem T3416_ok : Node.check D_R22222 T3416 [((0),(163/128)),((2025/512),(1215/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3417_ok T3418_ok
def T3415 : Node := Node.leaf L3415
theorem T3415_ok : Node.check D_R22222 T3415 [((163/256),(163/128)),((3645/1024),(2025/512)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3415_ok
def T3414 : Node := Node.leaf L3414
theorem T3414_ok : Node.check D_R22222 T3414 [((163/256),(163/128)),((405/128),(3645/1024)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3414_ok
def T3413 : Node := Node.split 1 T3414 T3415
theorem T3413_ok : Node.check D_R22222 T3413 [((163/256),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3414_ok T3415_ok
def T3412 : Node := Node.leaf L3412
theorem T3412_ok : Node.check D_R22222 T3412 [((163/256),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L3412_ok
def T3411 : Node := Node.split 3 T3412 T3413
theorem T3411_ok : Node.check D_R22222 T3411 [((163/256),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3412_ok T3413_ok
def T3410 : Node := Node.leaf L3410
theorem T3410_ok : Node.check D_R22222 T3410 [((0),(163/256)),((405/128),(2025/512)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3410_ok
def T3409 : Node := Node.split 0 T3410 T3411
theorem T3409_ok : Node.check D_R22222 T3409 [((0),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3410_ok T3411_ok
def T3408 : Node := Node.leaf L3408
theorem T3408_ok : Node.check D_R22222 T3408 [((0),(163/128)),((405/128),(2025/512)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3408_ok
def T3407 : Node := Node.split 2 T3408 T3409
theorem T3407_ok : Node.check D_R22222 T3407 [((0),(163/128)),((405/128),(2025/512)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3408_ok T3409_ok
def T3406 : Node := Node.split 1 T3407 T3416
theorem T3406_ok : Node.check D_R22222 T3406 [((0),(163/128)),((405/128),(1215/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3407_ok T3416_ok
def T3405 : Node := Node.leaf L3405
theorem T3405_ok : Node.check D_R22222 T3405 [((163/256),(163/128)),((4455/1024),(1215/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3405_ok
def T3404 : Node := Node.leaf L3404
theorem T3404_ok : Node.check D_R22222 T3404 [((163/256),(163/128)),((2025/512),(4455/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3404_ok
def T3403 : Node := Node.leaf L3403
theorem T3403_ok : Node.check D_R22222 T3403 [((489/512),(163/128)),((8505/2048),(4455/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3403_ok
def T3402 : Node := Node.leaf L3402
theorem T3402_ok : Node.check D_R22222 T3402 [((1141/1024),(163/128)),((2025/512),(8505/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3402_ok
def T3401 : Node := Node.leaf L3401
theorem T3401_ok : Node.check D_R22222 T3401 [((489/512),(1141/1024)),((2025/512),(8505/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L3401_ok
def T3400 : Node := Node.leaf L3400
theorem T3400_ok : Node.check D_R22222 T3400 [((489/512),(1141/1024)),((2025/512),(8505/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L3400_ok
def T3399 : Node := Node.split 3 T3400 T3401
theorem T3399_ok : Node.check D_R22222 T3399 [((489/512),(1141/1024)),((2025/512),(8505/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3400_ok T3401_ok
def T3398 : Node := Node.split 0 T3399 T3402
theorem T3398_ok : Node.check D_R22222 T3398 [((489/512),(163/128)),((2025/512),(8505/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3399_ok T3402_ok
def T3397 : Node := Node.leaf L3397
theorem T3397_ok : Node.check D_R22222 T3397 [((489/512),(163/128)),((2025/512),(8505/2048)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3397_ok
def T3396 : Node := Node.split 2 T3397 T3398
theorem T3396_ok : Node.check D_R22222 T3396 [((489/512),(163/128)),((2025/512),(8505/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3397_ok T3398_ok
def T3395 : Node := Node.split 1 T3396 T3403
theorem T3395_ok : Node.check D_R22222 T3395 [((489/512),(163/128)),((2025/512),(4455/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3396_ok T3403_ok
def T3394 : Node := Node.leaf L3394
theorem T3394_ok : Node.check D_R22222 T3394 [((489/512),(163/128)),((2025/512),(4455/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L3394_ok
def T3393 : Node := Node.split 3 T3394 T3395
theorem T3393_ok : Node.check D_R22222 T3393 [((489/512),(163/128)),((2025/512),(4455/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3394_ok T3395_ok
def T3392 : Node := Node.leaf L3392
theorem T3392_ok : Node.check D_R22222 T3392 [((163/256),(489/512)),((2025/512),(4455/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3392_ok
def T3391 : Node := Node.split 0 T3392 T3393
theorem T3391_ok : Node.check D_R22222 T3391 [((163/256),(163/128)),((2025/512),(4455/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3392_ok T3393_ok
def T3390 : Node := Node.split 2 T3391 T3404
theorem T3390_ok : Node.check D_R22222 T3390 [((163/256),(163/128)),((2025/512),(4455/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3391_ok T3404_ok
def T3389 : Node := Node.split 1 T3390 T3405
theorem T3389_ok : Node.check D_R22222 T3389 [((163/256),(163/128)),((2025/512),(1215/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3390_ok T3405_ok
def T3388 : Node := Node.leaf L3388
theorem T3388_ok : Node.check D_R22222 T3388 [((163/256),(163/128)),((2025/512),(1215/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3388_ok
def T3387 : Node := Node.split 3 T3388 T3389
theorem T3387_ok : Node.check D_R22222 T3387 [((163/256),(163/128)),((2025/512),(1215/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3388_ok T3389_ok
def T3386 : Node := Node.leaf L3386
theorem T3386_ok : Node.check D_R22222 T3386 [((0),(163/256)),((2025/512),(1215/256)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3386_ok
def T3385 : Node := Node.split 0 T3386 T3387
theorem T3385_ok : Node.check D_R22222 T3385 [((0),(163/128)),((2025/512),(1215/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3386_ok T3387_ok
def T3384 : Node := Node.leaf L3384
theorem T3384_ok : Node.check D_R22222 T3384 [((0),(163/128)),((2025/512),(1215/256)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3384_ok
def T3383 : Node := Node.split 2 T3384 T3385
theorem T3383_ok : Node.check D_R22222 T3383 [((0),(163/128)),((2025/512),(1215/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3384_ok T3385_ok
def T3382 : Node := Node.leaf L3382
theorem T3382_ok : Node.check D_R22222 T3382 [((163/256),(163/128)),((3645/1024),(2025/512)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3382_ok
def T3381 : Node := Node.leaf L3381
theorem T3381_ok : Node.check D_R22222 T3381 [((489/512),(163/128)),((7695/2048),(2025/512)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3381_ok
def T3380 : Node := Node.leaf L3380
theorem T3380_ok : Node.check D_R22222 T3380 [((489/512),(163/128)),((3645/1024),(7695/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3380_ok
def T3379 : Node := Node.split 1 T3380 T3381
theorem T3379_ok : Node.check D_R22222 T3379 [((489/512),(163/128)),((3645/1024),(2025/512)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3380_ok T3381_ok
def T3378 : Node := Node.leaf L3378
theorem T3378_ok : Node.check D_R22222 T3378 [((489/512),(163/128)),((3645/1024),(2025/512)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L3378_ok
def T3377 : Node := Node.split 3 T3378 T3379
theorem T3377_ok : Node.check D_R22222 T3377 [((489/512),(163/128)),((3645/1024),(2025/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3378_ok T3379_ok
def T3376 : Node := Node.leaf L3376
theorem T3376_ok : Node.check D_R22222 T3376 [((163/256),(489/512)),((3645/1024),(2025/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3376_ok
def T3375 : Node := Node.split 0 T3376 T3377
theorem T3375_ok : Node.check D_R22222 T3375 [((163/256),(163/128)),((3645/1024),(2025/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3376_ok T3377_ok
def T3374 : Node := Node.split 2 T3375 T3382
theorem T3374_ok : Node.check D_R22222 T3374 [((163/256),(163/128)),((3645/1024),(2025/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3375_ok T3382_ok
def T3373 : Node := Node.leaf L3373
theorem T3373_ok : Node.check D_R22222 T3373 [((163/256),(163/128)),((405/128),(3645/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3373_ok
def T3372 : Node := Node.leaf L3372
theorem T3372_ok : Node.check D_R22222 T3372 [((163/256),(163/128)),((405/128),(3645/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3372_ok
def T3371 : Node := Node.split 2 T3372 T3373
theorem T3371_ok : Node.check D_R22222 T3371 [((163/256),(163/128)),((405/128),(3645/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3372_ok T3373_ok
def T3370 : Node := Node.split 1 T3371 T3374
theorem T3370_ok : Node.check D_R22222 T3370 [((163/256),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3371_ok T3374_ok
def T3369 : Node := Node.leaf L3369
theorem T3369_ok : Node.check D_R22222 T3369 [((163/256),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3369_ok
def T3368 : Node := Node.split 3 T3369 T3370
theorem T3368_ok : Node.check D_R22222 T3368 [((163/256),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3369_ok T3370_ok
def T3367 : Node := Node.leaf L3367
theorem T3367_ok : Node.check D_R22222 T3367 [((0),(163/256)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3367_ok
def T3366 : Node := Node.split 0 T3367 T3368
theorem T3366_ok : Node.check D_R22222 T3366 [((0),(163/128)),((405/128),(2025/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3367_ok T3368_ok
def T3365 : Node := Node.leaf L3365
theorem T3365_ok : Node.check D_R22222 T3365 [((0),(163/128)),((405/128),(2025/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3365_ok
def T3364 : Node := Node.split 2 T3365 T3366
theorem T3364_ok : Node.check D_R22222 T3364 [((0),(163/128)),((405/128),(2025/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3365_ok T3366_ok
def T3363 : Node := Node.split 1 T3364 T3383
theorem T3363_ok : Node.check D_R22222 T3363 [((0),(163/128)),((405/128),(1215/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3364_ok T3383_ok
def T3362 : Node := Node.split 3 T3363 T3406
theorem T3362_ok : Node.check D_R22222 T3362 [((0),(163/128)),((405/128),(1215/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3363_ok T3406_ok
def T3361 : Node := Node.split 0 T3362 T3423
theorem T3361_ok : Node.check D_R22222 T3361 [((0),(163/64)),((405/128),(1215/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3362_ok T3423_ok
def T3360 : Node := Node.split 2 T3361 T3456
theorem T3360_ok : Node.check D_R22222 T3360 [((0),(163/64)),((405/128),(1215/256)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3361_ok T3456_ok
def T3359 : Node := Node.split 1 T3360 T3501
theorem T3359_ok : Node.check D_R22222 T3359 [((0),(163/64)),((405/128),(405/64)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3360_ok T3501_ok
def T3358 : Node := Node.split 3 T3359 T3534
theorem T3358_ok : Node.check D_R22222 T3358 [((0),(163/64)),((405/128),(405/64)),((0),(405/128)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3359_ok T3534_ok
def T3357 : Node := Node.split 0 T3358 T3563
theorem T3357_ok : Node.check D_R22222 T3357 [((0),(163/32)),((405/128),(405/64)),((0),(405/128)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3358_ok T3563_ok
def T3356 : Node := Node.split 2 T3357 T3596
theorem T3356_ok : Node.check D_R22222 T3356 [((0),(163/32)),((405/128),(405/64)),((0),(405/64)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3357_ok T3596_ok
def T3355 : Node := Node.leaf L3355
theorem T3355_ok : Node.check D_R22222 T3355 [((163/64),(163/32)),((0),(405/128)),((405/128),(405/64)),((163/64),(163/32))] = true := Node.check_leaf_of _ _ _ L3355_ok
def T3354 : Node := Node.leaf L3354
theorem T3354_ok : Node.check D_R22222 T3354 [((163/64),(163/32)),((405/256),(405/128)),((405/128),(405/64)),((0),(163/64))] = true := Node.check_leaf_of _ _ _ L3354_ok
def T3353 : Node := Node.leaf L3353
theorem T3353_ok : Node.check D_R22222 T3353 [((163/64),(163/32)),((0),(405/256)),((1215/256),(405/64)),((0),(163/64))] = true := Node.check_leaf_of _ _ _ L3353_ok
def T3352 : Node := Node.leaf L3352
theorem T3352_ok : Node.check D_R22222 T3352 [((489/128),(163/32)),((0),(405/256)),((405/128),(1215/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3352_ok
def T3351 : Node := Node.leaf L3351
theorem T3351_ok : Node.check D_R22222 T3351 [((489/128),(163/32)),((405/512),(405/256)),((405/128),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3351_ok
def T3350 : Node := Node.leaf L3350
theorem T3350_ok : Node.check D_R22222 T3350 [((489/128),(163/32)),((0),(405/512)),((405/128),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3350_ok
def T3349 : Node := Node.split 1 T3350 T3351
theorem T3349_ok : Node.check D_R22222 T3349 [((489/128),(163/32)),((0),(405/256)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3350_ok T3351_ok
def T3348 : Node := Node.split 3 T3349 T3352
theorem T3348_ok : Node.check D_R22222 T3348 [((489/128),(163/32)),((0),(405/256)),((405/128),(1215/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3349_ok T3352_ok
def T3347 : Node := Node.leaf L3347
theorem T3347_ok : Node.check D_R22222 T3347 [((163/64),(489/128)),((405/512),(405/256)),((405/128),(1215/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3347_ok
def T3346 : Node := Node.leaf L3346
theorem T3346_ok : Node.check D_R22222 T3346 [((163/64),(489/128)),((0),(405/512)),((405/128),(1215/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3346_ok
def T3345 : Node := Node.split 1 T3346 T3347
theorem T3345_ok : Node.check D_R22222 T3345 [((163/64),(489/128)),((0),(405/256)),((405/128),(1215/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3346_ok T3347_ok
def T3344 : Node := Node.leaf L3344
theorem T3344_ok : Node.check D_R22222 T3344 [((163/64),(489/128)),((405/512),(405/256)),((2025/512),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3344_ok
def T3343 : Node := Node.leaf L3343
theorem T3343_ok : Node.check D_R22222 T3343 [((815/256),(489/128)),((405/512),(405/256)),((405/128),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3343_ok
def T3342 : Node := Node.leaf L3342
theorem T3342_ok : Node.check D_R22222 T3342 [((815/256),(489/128)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3342_ok
def T3341 : Node := Node.split 3 T3342 T3343
theorem T3341_ok : Node.check D_R22222 T3341 [((815/256),(489/128)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3342_ok T3343_ok
def T3340 : Node := Node.leaf L3340
theorem T3340_ok : Node.check D_R22222 T3340 [((163/64),(815/256)),((405/512),(405/256)),((405/128),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3340_ok
def T3339 : Node := Node.leaf L3339
theorem T3339_ok : Node.check D_R22222 T3339 [((163/64),(815/256)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3339_ok
def T3338 : Node := Node.split 3 T3339 T3340
theorem T3338_ok : Node.check D_R22222 T3338 [((163/64),(815/256)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3339_ok T3340_ok
def T3337 : Node := Node.split 0 T3338 T3341
theorem T3337_ok : Node.check D_R22222 T3337 [((163/64),(489/128)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3338_ok T3341_ok
def T3336 : Node := Node.split 2 T3337 T3344
theorem T3336_ok : Node.check D_R22222 T3336 [((163/64),(489/128)),((405/512),(405/256)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3337_ok T3344_ok
def T3335 : Node := Node.leaf L3335
theorem T3335_ok : Node.check D_R22222 T3335 [((163/64),(489/128)),((0),(405/512)),((405/128),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3335_ok
def T3334 : Node := Node.split 1 T3335 T3336
theorem T3334_ok : Node.check D_R22222 T3334 [((163/64),(489/128)),((0),(405/256)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3335_ok T3336_ok
def T3333 : Node := Node.split 3 T3334 T3345
theorem T3333_ok : Node.check D_R22222 T3333 [((163/64),(489/128)),((0),(405/256)),((405/128),(1215/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3334_ok T3345_ok
def T3332 : Node := Node.split 0 T3333 T3348
theorem T3332_ok : Node.check D_R22222 T3332 [((163/64),(163/32)),((0),(405/256)),((405/128),(1215/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3333_ok T3348_ok
def T3331 : Node := Node.split 2 T3332 T3353
theorem T3331_ok : Node.check D_R22222 T3331 [((163/64),(163/32)),((0),(405/256)),((405/128),(405/64)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3332_ok T3353_ok
def T3330 : Node := Node.split 1 T3331 T3354
theorem T3330_ok : Node.check D_R22222 T3330 [((163/64),(163/32)),((0),(405/128)),((405/128),(405/64)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3331_ok T3354_ok
def T3329 : Node := Node.split 3 T3330 T3355
theorem T3329_ok : Node.check D_R22222 T3329 [((163/64),(163/32)),((0),(405/128)),((405/128),(405/64)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3330_ok T3355_ok
def T3328 : Node := Node.leaf L3328
theorem T3328_ok : Node.check D_R22222 T3328 [((0),(163/64)),((405/256),(405/128)),((405/128),(405/64)),((163/64),(163/32))] = true := Node.check_leaf_of _ _ _ L3328_ok
def T3327 : Node := Node.leaf L3327
theorem T3327_ok : Node.check D_R22222 T3327 [((0),(163/64)),((0),(405/256)),((1215/256),(405/64)),((163/64),(163/32))] = true := Node.check_leaf_of _ _ _ L3327_ok
def T3326 : Node := Node.leaf L3326
theorem T3326_ok : Node.check D_R22222 T3326 [((163/128),(163/64)),((0),(405/256)),((405/128),(1215/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3326_ok
def T3325 : Node := Node.leaf L3325
theorem T3325_ok : Node.check D_R22222 T3325 [((163/128),(163/64)),((405/512),(405/256)),((405/128),(1215/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3325_ok
def T3324 : Node := Node.leaf L3324
theorem T3324_ok : Node.check D_R22222 T3324 [((163/128),(163/64)),((0),(405/512)),((405/128),(1215/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3324_ok
def T3323 : Node := Node.split 1 T3324 T3325
theorem T3323_ok : Node.check D_R22222 T3323 [((163/128),(163/64)),((0),(405/256)),((405/128),(1215/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3324_ok T3325_ok
def T3322 : Node := Node.split 3 T3323 T3326
theorem T3322_ok : Node.check D_R22222 T3322 [((163/128),(163/64)),((0),(405/256)),((405/128),(1215/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3323_ok T3326_ok
def T3321 : Node := Node.leaf L3321
theorem T3321_ok : Node.check D_R22222 T3321 [((0),(163/128)),((405/512),(405/256)),((405/128),(1215/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3321_ok
def T3320 : Node := Node.leaf L3320
theorem T3320_ok : Node.check D_R22222 T3320 [((0),(163/128)),((0),(405/512)),((405/128),(1215/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3320_ok
def T3319 : Node := Node.split 1 T3320 T3321
theorem T3319_ok : Node.check D_R22222 T3319 [((0),(163/128)),((0),(405/256)),((405/128),(1215/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3320_ok T3321_ok
def T3318 : Node := Node.leaf L3318
theorem T3318_ok : Node.check D_R22222 T3318 [((0),(163/128)),((405/512),(405/256)),((2025/512),(1215/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3318_ok
def T3317 : Node := Node.leaf L3317
theorem T3317_ok : Node.check D_R22222 T3317 [((163/256),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L3317_ok
def T3316 : Node := Node.leaf L3316
theorem T3316_ok : Node.check D_R22222 T3316 [((163/256),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3316_ok
def T3315 : Node := Node.split 3 T3316 T3317
theorem T3315_ok : Node.check D_R22222 T3315 [((163/256),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3316_ok T3317_ok
def T3314 : Node := Node.leaf L3314
theorem T3314_ok : Node.check D_R22222 T3314 [((0),(163/256)),((405/512),(405/256)),((405/128),(2025/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3314_ok
def T3313 : Node := Node.split 0 T3314 T3315
theorem T3313_ok : Node.check D_R22222 T3313 [((0),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3314_ok T3315_ok
def T3312 : Node := Node.split 2 T3313 T3318
theorem T3312_ok : Node.check D_R22222 T3312 [((0),(163/128)),((405/512),(405/256)),((405/128),(1215/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3313_ok T3318_ok
def T3311 : Node := Node.leaf L3311
theorem T3311_ok : Node.check D_R22222 T3311 [((0),(163/128)),((0),(405/512)),((405/128),(1215/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3311_ok
def T3310 : Node := Node.split 1 T3311 T3312
theorem T3310_ok : Node.check D_R22222 T3310 [((0),(163/128)),((0),(405/256)),((405/128),(1215/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3311_ok T3312_ok
def T3309 : Node := Node.split 3 T3310 T3319
theorem T3309_ok : Node.check D_R22222 T3309 [((0),(163/128)),((0),(405/256)),((405/128),(1215/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3310_ok T3319_ok
def T3308 : Node := Node.split 0 T3309 T3322
theorem T3308_ok : Node.check D_R22222 T3308 [((0),(163/64)),((0),(405/256)),((405/128),(1215/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3309_ok T3322_ok
def T3307 : Node := Node.split 2 T3308 T3327
theorem T3307_ok : Node.check D_R22222 T3307 [((0),(163/64)),((0),(405/256)),((405/128),(405/64)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3308_ok T3327_ok
def T3306 : Node := Node.split 1 T3307 T3328
theorem T3306_ok : Node.check D_R22222 T3306 [((0),(163/64)),((0),(405/128)),((405/128),(405/64)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3307_ok T3328_ok
def T3305 : Node := Node.leaf L3305
theorem T3305_ok : Node.check D_R22222 T3305 [((0),(163/64)),((405/256),(405/128)),((1215/256),(405/64)),((0),(163/64))] = true := Node.check_leaf_of _ _ _ L3305_ok
def T3304 : Node := Node.leaf L3304
theorem T3304_ok : Node.check D_R22222 T3304 [((163/128),(163/64)),((405/256),(405/128)),((405/128),(1215/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3304_ok
def T3303 : Node := Node.leaf L3303
theorem T3303_ok : Node.check D_R22222 T3303 [((163/128),(163/64)),((1215/512),(405/128)),((405/128),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3303_ok
def T3302 : Node := Node.leaf L3302
theorem T3302_ok : Node.check D_R22222 T3302 [((163/128),(163/64)),((405/256),(1215/512)),((2025/512),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3302_ok
def T3301 : Node := Node.leaf L3301
theorem T3301_ok : Node.check D_R22222 T3301 [((489/256),(163/64)),((405/256),(1215/512)),((405/128),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3301_ok
def T3300 : Node := Node.leaf L3300
theorem T3300_ok : Node.check D_R22222 T3300 [((489/256),(163/64)),((405/256),(1215/512)),((405/128),(2025/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3300_ok
def T3299 : Node := Node.split 3 T3300 T3301
theorem T3299_ok : Node.check D_R22222 T3299 [((489/256),(163/64)),((405/256),(1215/512)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3300_ok T3301_ok
def T3298 : Node := Node.leaf L3298
theorem T3298_ok : Node.check D_R22222 T3298 [((163/128),(489/256)),((405/256),(1215/512)),((405/128),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3298_ok
def T3297 : Node := Node.leaf L3297
theorem T3297_ok : Node.check D_R22222 T3297 [((163/128),(489/256)),((405/256),(1215/512)),((405/128),(2025/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3297_ok
def T3296 : Node := Node.split 3 T3297 T3298
theorem T3296_ok : Node.check D_R22222 T3296 [((163/128),(489/256)),((405/256),(1215/512)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3297_ok T3298_ok
def T3295 : Node := Node.split 0 T3296 T3299
theorem T3295_ok : Node.check D_R22222 T3295 [((163/128),(163/64)),((405/256),(1215/512)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3296_ok T3299_ok
def T3294 : Node := Node.split 2 T3295 T3302
theorem T3294_ok : Node.check D_R22222 T3294 [((163/128),(163/64)),((405/256),(1215/512)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3295_ok T3302_ok
def T3293 : Node := Node.split 1 T3294 T3303
theorem T3293_ok : Node.check D_R22222 T3293 [((163/128),(163/64)),((405/256),(405/128)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3294_ok T3303_ok
def T3292 : Node := Node.split 3 T3293 T3304
theorem T3292_ok : Node.check D_R22222 T3292 [((163/128),(163/64)),((405/256),(405/128)),((405/128),(1215/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3293_ok T3304_ok
def T3291 : Node := Node.leaf L3291
theorem T3291_ok : Node.check D_R22222 T3291 [((0),(163/128)),((1215/512),(405/128)),((405/128),(1215/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3291_ok
def T3290 : Node := Node.leaf L3290
theorem T3290_ok : Node.check D_R22222 T3290 [((0),(163/128)),((405/256),(1215/512)),((2025/512),(1215/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3290_ok
def T3289 : Node := Node.leaf L3289
theorem T3289_ok : Node.check D_R22222 T3289 [((163/256),(163/128)),((405/256),(1215/512)),((405/128),(2025/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3289_ok
def T3288 : Node := Node.leaf L3288
theorem T3288_ok : Node.check D_R22222 T3288 [((163/256),(163/128)),((405/256),(1215/512)),((405/128),(2025/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L3288_ok
def T3287 : Node := Node.split 3 T3288 T3289
theorem T3287_ok : Node.check D_R22222 T3287 [((163/256),(163/128)),((405/256),(1215/512)),((405/128),(2025/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3288_ok T3289_ok
def T3286 : Node := Node.leaf L3286
theorem T3286_ok : Node.check D_R22222 T3286 [((0),(163/256)),((405/256),(1215/512)),((405/128),(2025/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3286_ok
def T3285 : Node := Node.split 0 T3286 T3287
theorem T3285_ok : Node.check D_R22222 T3285 [((0),(163/128)),((405/256),(1215/512)),((405/128),(2025/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3286_ok T3287_ok
def T3284 : Node := Node.split 2 T3285 T3290
theorem T3284_ok : Node.check D_R22222 T3284 [((0),(163/128)),((405/256),(1215/512)),((405/128),(1215/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3285_ok T3290_ok
def T3283 : Node := Node.split 1 T3284 T3291
theorem T3283_ok : Node.check D_R22222 T3283 [((0),(163/128)),((405/256),(405/128)),((405/128),(1215/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3284_ok T3291_ok
def T3282 : Node := Node.leaf L3282
theorem T3282_ok : Node.check D_R22222 T3282 [((0),(163/128)),((1215/512),(405/128)),((2025/512),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3282_ok
def T3281 : Node := Node.leaf L3281
theorem T3281_ok : Node.check D_R22222 T3281 [((163/256),(163/128)),((1215/512),(405/128)),((405/128),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3281_ok
def T3280 : Node := Node.leaf L3280
theorem T3280_ok : Node.check D_R22222 T3280 [((163/256),(163/128)),((1215/512),(405/128)),((405/128),(2025/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3280_ok
def T3279 : Node := Node.split 3 T3280 T3281
theorem T3279_ok : Node.check D_R22222 T3279 [((163/256),(163/128)),((1215/512),(405/128)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3280_ok T3281_ok
def T3278 : Node := Node.leaf L3278
theorem T3278_ok : Node.check D_R22222 T3278 [((0),(163/256)),((1215/512),(405/128)),((405/128),(2025/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3278_ok
def T3277 : Node := Node.split 0 T3278 T3279
theorem T3277_ok : Node.check D_R22222 T3277 [((0),(163/128)),((1215/512),(405/128)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3278_ok T3279_ok
def T3276 : Node := Node.split 2 T3277 T3282
theorem T3276_ok : Node.check D_R22222 T3276 [((0),(163/128)),((1215/512),(405/128)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3277_ok T3282_ok
def T3275 : Node := Node.leaf L3275
theorem T3275_ok : Node.check D_R22222 T3275 [((163/256),(163/128)),((405/256),(1215/512)),((2025/512),(1215/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3275_ok
def T3274 : Node := Node.leaf L3274
theorem T3274_ok : Node.check D_R22222 T3274 [((163/256),(163/128)),((405/256),(1215/512)),((2025/512),(1215/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3274_ok
def T3273 : Node := Node.split 3 T3274 T3275
theorem T3273_ok : Node.check D_R22222 T3273 [((163/256),(163/128)),((405/256),(1215/512)),((2025/512),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3274_ok T3275_ok
def T3272 : Node := Node.leaf L3272
theorem T3272_ok : Node.check D_R22222 T3272 [((0),(163/256)),((405/256),(1215/512)),((2025/512),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3272_ok
def T3271 : Node := Node.split 0 T3272 T3273
theorem T3271_ok : Node.check D_R22222 T3271 [((0),(163/128)),((405/256),(1215/512)),((2025/512),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3272_ok T3273_ok
def T3270 : Node := Node.leaf L3270
theorem T3270_ok : Node.check D_R22222 T3270 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/128),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3270_ok
def T3269 : Node := Node.leaf L3269
theorem T3269_ok : Node.check D_R22222 T3269 [((163/256),(163/128)),((405/256),(2025/1024)),((405/128),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3269_ok
def T3268 : Node := Node.split 1 T3269 T3270
theorem T3268_ok : Node.check D_R22222 T3268 [((163/256),(163/128)),((405/256),(1215/512)),((405/128),(2025/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3269_ok T3270_ok
def T3267 : Node := Node.leaf L3267
theorem T3267_ok : Node.check D_R22222 T3267 [((163/256),(163/128)),((405/256),(1215/512)),((405/128),(2025/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3267_ok
def T3266 : Node := Node.split 3 T3267 T3268
theorem T3266_ok : Node.check D_R22222 T3266 [((163/256),(163/128)),((405/256),(1215/512)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3267_ok T3268_ok
def T3265 : Node := Node.leaf L3265
theorem T3265_ok : Node.check D_R22222 T3265 [((0),(163/256)),((405/256),(1215/512)),((405/128),(2025/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3265_ok
def T3264 : Node := Node.split 0 T3265 T3266
theorem T3264_ok : Node.check D_R22222 T3264 [((0),(163/128)),((405/256),(1215/512)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3265_ok T3266_ok
def T3263 : Node := Node.split 2 T3264 T3271
theorem T3263_ok : Node.check D_R22222 T3263 [((0),(163/128)),((405/256),(1215/512)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3264_ok T3271_ok
def T3262 : Node := Node.split 1 T3263 T3276
theorem T3262_ok : Node.check D_R22222 T3262 [((0),(163/128)),((405/256),(405/128)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3263_ok T3276_ok
def T3261 : Node := Node.split 3 T3262 T3283
theorem T3261_ok : Node.check D_R22222 T3261 [((0),(163/128)),((405/256),(405/128)),((405/128),(1215/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3262_ok T3283_ok
def T3260 : Node := Node.split 0 T3261 T3292
theorem T3260_ok : Node.check D_R22222 T3260 [((0),(163/64)),((405/256),(405/128)),((405/128),(1215/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3261_ok T3292_ok
def T3259 : Node := Node.split 2 T3260 T3305
theorem T3259_ok : Node.check D_R22222 T3259 [((0),(163/64)),((405/256),(405/128)),((405/128),(405/64)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3260_ok T3305_ok
def T3258 : Node := Node.leaf L3258
theorem T3258_ok : Node.check D_R22222 T3258 [((163/128),(163/64)),((0),(405/256)),((1215/256),(405/64)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3258_ok
def T3257 : Node := Node.leaf L3257
theorem T3257_ok : Node.check D_R22222 T3257 [((163/128),(163/64)),((405/512),(405/256)),((1215/256),(405/64)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3257_ok
def T3256 : Node := Node.leaf L3256
theorem T3256_ok : Node.check D_R22222 T3256 [((163/128),(163/64)),((0),(405/512)),((1215/256),(405/64)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3256_ok
def T3255 : Node := Node.split 1 T3256 T3257
theorem T3255_ok : Node.check D_R22222 T3255 [((163/128),(163/64)),((0),(405/256)),((1215/256),(405/64)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3256_ok T3257_ok
def T3254 : Node := Node.split 3 T3255 T3258
theorem T3254_ok : Node.check D_R22222 T3254 [((163/128),(163/64)),((0),(405/256)),((1215/256),(405/64)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3255_ok T3258_ok
def T3253 : Node := Node.leaf L3253
theorem T3253_ok : Node.check D_R22222 T3253 [((0),(163/128)),((405/512),(405/256)),((1215/256),(405/64)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3253_ok
def T3252 : Node := Node.leaf L3252
theorem T3252_ok : Node.check D_R22222 T3252 [((0),(163/128)),((0),(405/512)),((1215/256),(405/64)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3252_ok
def T3251 : Node := Node.split 1 T3252 T3253
theorem T3251_ok : Node.check D_R22222 T3251 [((0),(163/128)),((0),(405/256)),((1215/256),(405/64)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3252_ok T3253_ok
def T3250 : Node := Node.leaf L3250
theorem T3250_ok : Node.check D_R22222 T3250 [((0),(163/128)),((405/512),(405/256)),((2835/512),(405/64)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3250_ok
def T3249 : Node := Node.leaf L3249
theorem T3249_ok : Node.check D_R22222 T3249 [((163/256),(163/128)),((405/512),(405/256)),((1215/256),(2835/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3249_ok
def T3248 : Node := Node.leaf L3248
theorem T3248_ok : Node.check D_R22222 T3248 [((163/256),(163/128)),((405/512),(405/256)),((1215/256),(2835/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3248_ok
def T3247 : Node := Node.split 3 T3248 T3249
theorem T3247_ok : Node.check D_R22222 T3247 [((163/256),(163/128)),((405/512),(405/256)),((1215/256),(2835/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3248_ok T3249_ok
def T3246 : Node := Node.leaf L3246
theorem T3246_ok : Node.check D_R22222 T3246 [((0),(163/256)),((405/512),(405/256)),((1215/256),(2835/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3246_ok
def T3245 : Node := Node.split 0 T3246 T3247
theorem T3245_ok : Node.check D_R22222 T3245 [((0),(163/128)),((405/512),(405/256)),((1215/256),(2835/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3246_ok T3247_ok
def T3244 : Node := Node.split 2 T3245 T3250
theorem T3244_ok : Node.check D_R22222 T3244 [((0),(163/128)),((405/512),(405/256)),((1215/256),(405/64)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3245_ok T3250_ok
def T3243 : Node := Node.leaf L3243
theorem T3243_ok : Node.check D_R22222 T3243 [((0),(163/128)),((0),(405/512)),((1215/256),(405/64)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3243_ok
def T3242 : Node := Node.split 1 T3243 T3244
theorem T3242_ok : Node.check D_R22222 T3242 [((0),(163/128)),((0),(405/256)),((1215/256),(405/64)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3243_ok T3244_ok
def T3241 : Node := Node.split 3 T3242 T3251
theorem T3241_ok : Node.check D_R22222 T3241 [((0),(163/128)),((0),(405/256)),((1215/256),(405/64)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3242_ok T3251_ok
def T3240 : Node := Node.split 0 T3241 T3254
theorem T3240_ok : Node.check D_R22222 T3240 [((0),(163/64)),((0),(405/256)),((1215/256),(405/64)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3241_ok T3254_ok
def T3239 : Node := Node.leaf L3239
theorem T3239_ok : Node.check D_R22222 T3239 [((163/128),(163/64)),((405/512),(405/256)),((2025/512),(1215/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3239_ok
def T3238 : Node := Node.leaf L3238
theorem T3238_ok : Node.check D_R22222 T3238 [((489/256),(163/64)),((405/512),(405/256)),((405/128),(2025/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3238_ok
def T3237 : Node := Node.leaf L3237
theorem T3237_ok : Node.check D_R22222 T3237 [((489/256),(163/64)),((405/512),(405/256)),((405/128),(2025/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L3237_ok
def T3236 : Node := Node.split 3 T3237 T3238
theorem T3236_ok : Node.check D_R22222 T3236 [((489/256),(163/64)),((405/512),(405/256)),((405/128),(2025/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3237_ok T3238_ok
def T3235 : Node := Node.leaf L3235
theorem T3235_ok : Node.check D_R22222 T3235 [((163/128),(489/256)),((405/512),(405/256)),((405/128),(2025/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3235_ok
def T3234 : Node := Node.split 0 T3235 T3236
theorem T3234_ok : Node.check D_R22222 T3234 [((163/128),(163/64)),((405/512),(405/256)),((405/128),(2025/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3235_ok T3236_ok
def T3233 : Node := Node.split 2 T3234 T3239
theorem T3233_ok : Node.check D_R22222 T3233 [((163/128),(163/64)),((405/512),(405/256)),((405/128),(1215/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3234_ok T3239_ok
def T3232 : Node := Node.leaf L3232
theorem T3232_ok : Node.check D_R22222 T3232 [((163/128),(163/64)),((0),(405/512)),((405/128),(1215/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3232_ok
def T3231 : Node := Node.split 1 T3232 T3233
theorem T3231_ok : Node.check D_R22222 T3231 [((163/128),(163/64)),((0),(405/256)),((405/128),(1215/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3232_ok T3233_ok
def T3230 : Node := Node.leaf L3230
theorem T3230_ok : Node.check D_R22222 T3230 [((489/256),(163/64)),((405/512),(405/256)),((2025/512),(1215/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3230_ok
def T3229 : Node := Node.leaf L3229
theorem T3229_ok : Node.check D_R22222 T3229 [((489/256),(163/64)),((405/512),(405/256)),((2025/512),(1215/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3229_ok
def T3228 : Node := Node.split 3 T3229 T3230
theorem T3228_ok : Node.check D_R22222 T3228 [((489/256),(163/64)),((405/512),(405/256)),((2025/512),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3229_ok T3230_ok
def T3227 : Node := Node.leaf L3227
theorem T3227_ok : Node.check D_R22222 T3227 [((163/128),(489/256)),((405/512),(405/256)),((2025/512),(1215/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3227_ok
def T3226 : Node := Node.leaf L3226
theorem T3226_ok : Node.check D_R22222 T3226 [((163/128),(489/256)),((405/512),(405/256)),((2025/512),(1215/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3226_ok
def T3225 : Node := Node.split 3 T3226 T3227
theorem T3225_ok : Node.check D_R22222 T3225 [((163/128),(489/256)),((405/512),(405/256)),((2025/512),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3226_ok T3227_ok
def T3224 : Node := Node.split 0 T3225 T3228
theorem T3224_ok : Node.check D_R22222 T3224 [((163/128),(163/64)),((405/512),(405/256)),((2025/512),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3225_ok T3228_ok
def T3223 : Node := Node.leaf L3223
theorem T3223_ok : Node.check D_R22222 T3223 [((489/256),(163/64)),((1215/1024),(405/256)),((405/128),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3223_ok
def T3222 : Node := Node.leaf L3222
theorem T3222_ok : Node.check D_R22222 T3222 [((489/256),(163/64)),((405/512),(1215/1024)),((3645/1024),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3222_ok
def T3221 : Node := Node.leaf L3221
theorem T3221_ok : Node.check D_R22222 T3221 [((489/256),(163/64)),((405/512),(1215/1024)),((405/128),(3645/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3221_ok
def T3220 : Node := Node.split 2 T3221 T3222
theorem T3220_ok : Node.check D_R22222 T3220 [((489/256),(163/64)),((405/512),(1215/1024)),((405/128),(2025/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3221_ok T3222_ok
def T3219 : Node := Node.split 1 T3220 T3223
theorem T3219_ok : Node.check D_R22222 T3219 [((489/256),(163/64)),((405/512),(405/256)),((405/128),(2025/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3220_ok T3223_ok
def T3218 : Node := Node.leaf L3218
theorem T3218_ok : Node.check D_R22222 T3218 [((489/256),(163/64)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3218_ok
def T3217 : Node := Node.split 3 T3218 T3219
theorem T3217_ok : Node.check D_R22222 T3217 [((489/256),(163/64)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3218_ok T3219_ok
def T3216 : Node := Node.leaf L3216
theorem T3216_ok : Node.check D_R22222 T3216 [((163/128),(489/256)),((405/512),(405/256)),((405/128),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3216_ok
def T3215 : Node := Node.leaf L3215
theorem T3215_ok : Node.check D_R22222 T3215 [((163/128),(489/256)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3215_ok
def T3214 : Node := Node.split 3 T3215 T3216
theorem T3214_ok : Node.check D_R22222 T3214 [((163/128),(489/256)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3215_ok T3216_ok
def T3213 : Node := Node.split 0 T3214 T3217
theorem T3213_ok : Node.check D_R22222 T3213 [((163/128),(163/64)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3214_ok T3217_ok
def T3212 : Node := Node.split 2 T3213 T3224
theorem T3212_ok : Node.check D_R22222 T3212 [((163/128),(163/64)),((405/512),(405/256)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3213_ok T3224_ok
def T3211 : Node := Node.leaf L3211
theorem T3211_ok : Node.check D_R22222 T3211 [((163/128),(163/64)),((0),(405/512)),((405/128),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3211_ok
def T3210 : Node := Node.split 1 T3211 T3212
theorem T3210_ok : Node.check D_R22222 T3210 [((163/128),(163/64)),((0),(405/256)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3211_ok T3212_ok
def T3209 : Node := Node.split 3 T3210 T3231
theorem T3209_ok : Node.check D_R22222 T3209 [((163/128),(163/64)),((0),(405/256)),((405/128),(1215/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3210_ok T3231_ok
def T3208 : Node := Node.leaf L3208
theorem T3208_ok : Node.check D_R22222 T3208 [((163/256),(163/128)),((405/512),(405/256)),((2025/512),(1215/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3208_ok
def T3207 : Node := Node.leaf L3207
theorem T3207_ok : Node.check D_R22222 T3207 [((163/256),(163/128)),((405/512),(405/256)),((2025/512),(1215/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L3207_ok
def T3206 : Node := Node.split 3 T3207 T3208
theorem T3206_ok : Node.check D_R22222 T3206 [((163/256),(163/128)),((405/512),(405/256)),((2025/512),(1215/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3207_ok T3208_ok
def T3205 : Node := Node.leaf L3205
theorem T3205_ok : Node.check D_R22222 T3205 [((0),(163/256)),((405/512),(405/256)),((2025/512),(1215/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3205_ok
def T3204 : Node := Node.split 0 T3205 T3206
theorem T3204_ok : Node.check D_R22222 T3204 [((0),(163/128)),((405/512),(405/256)),((2025/512),(1215/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3205_ok T3206_ok
def T3203 : Node := Node.leaf L3203
theorem T3203_ok : Node.check D_R22222 T3203 [((163/256),(163/128)),((1215/1024),(405/256)),((405/128),(2025/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3203_ok
def T3202 : Node := Node.leaf L3202
theorem T3202_ok : Node.check D_R22222 T3202 [((163/256),(163/128)),((405/512),(1215/1024)),((3645/1024),(2025/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3202_ok
def T3201 : Node := Node.leaf L3201
theorem T3201_ok : Node.check D_R22222 T3201 [((163/256),(163/128)),((405/512),(1215/1024)),((405/128),(3645/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L3201_ok
def T3200 : Node := Node.split 2 T3201 T3202
theorem T3200_ok : Node.check D_R22222 T3200 [((163/256),(163/128)),((405/512),(1215/1024)),((405/128),(2025/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3201_ok T3202_ok
def T3199 : Node := Node.split 1 T3200 T3203
theorem T3199_ok : Node.check D_R22222 T3199 [((163/256),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3200_ok T3203_ok
def T3198 : Node := Node.leaf L3198
theorem T3198_ok : Node.check D_R22222 T3198 [((163/256),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L3198_ok
def T3197 : Node := Node.split 3 T3198 T3199
theorem T3197_ok : Node.check D_R22222 T3197 [((163/256),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3198_ok T3199_ok
def T3196 : Node := Node.leaf L3196
theorem T3196_ok : Node.check D_R22222 T3196 [((0),(163/256)),((405/512),(405/256)),((405/128),(2025/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3196_ok
def T3195 : Node := Node.split 0 T3196 T3197
theorem T3195_ok : Node.check D_R22222 T3195 [((0),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3196_ok T3197_ok
def T3194 : Node := Node.split 2 T3195 T3204
theorem T3194_ok : Node.check D_R22222 T3194 [((0),(163/128)),((405/512),(405/256)),((405/128),(1215/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3195_ok T3204_ok
def T3193 : Node := Node.leaf L3193
theorem T3193_ok : Node.check D_R22222 T3193 [((0),(163/128)),((0),(405/512)),((405/128),(1215/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L3193_ok
def T3192 : Node := Node.split 1 T3193 T3194
theorem T3192_ok : Node.check D_R22222 T3192 [((0),(163/128)),((0),(405/256)),((405/128),(1215/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3193_ok T3194_ok
def T3191 : Node := Node.leaf L3191
theorem T3191_ok : Node.check D_R22222 T3191 [((163/256),(163/128)),((1215/1024),(405/256)),((2025/512),(1215/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3191_ok
def T3190 : Node := Node.leaf L3190
theorem T3190_ok : Node.check D_R22222 T3190 [((163/256),(163/128)),((405/512),(1215/1024)),((4455/1024),(1215/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3190_ok
def T3189 : Node := Node.leaf L3189
theorem T3189_ok : Node.check D_R22222 T3189 [((489/512),(163/128)),((2025/2048),(1215/1024)),((8505/2048),(4455/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3189_ok
def T3188 : Node := Node.leaf L3188
theorem T3188_ok : Node.check D_R22222 T3188 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/512),(8505/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3188_ok
def T3187 : Node := Node.leaf L3187
theorem T3187_ok : Node.check D_R22222 T3187 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/512),(8505/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L3187_ok
def T3186 : Node := Node.leaf L3186
theorem T3186_ok : Node.check D_R22222 T3186 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/512),(8505/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L3186_ok
def T3185 : Node := Node.split 3 T3186 T3187
theorem T3185_ok : Node.check D_R22222 T3185 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/512),(8505/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3186_ok T3187_ok
def T3184 : Node := Node.split 0 T3185 T3188
theorem T3184_ok : Node.check D_R22222 T3184 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/512),(8505/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3185_ok T3188_ok
def T3183 : Node := Node.split 2 T3184 T3189
theorem T3183_ok : Node.check D_R22222 T3183 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/512),(4455/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3184_ok T3189_ok
def T3182 : Node := Node.leaf L3182
theorem T3182_ok : Node.check D_R22222 T3182 [((489/512),(163/128)),((405/512),(2025/2048)),((2025/512),(4455/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3182_ok
def T3181 : Node := Node.split 1 T3182 T3183
theorem T3181_ok : Node.check D_R22222 T3181 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/512),(4455/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3182_ok T3183_ok
def T3180 : Node := Node.leaf L3180
theorem T3180_ok : Node.check D_R22222 T3180 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/512),(4455/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L3180_ok
def T3179 : Node := Node.split 3 T3180 T3181
theorem T3179_ok : Node.check D_R22222 T3179 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/512),(4455/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3180_ok T3181_ok
def T3178 : Node := Node.leaf L3178
theorem T3178_ok : Node.check D_R22222 T3178 [((163/256),(489/512)),((405/512),(1215/1024)),((2025/512),(4455/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3178_ok
def T3177 : Node := Node.split 0 T3178 T3179
theorem T3177_ok : Node.check D_R22222 T3177 [((163/256),(163/128)),((405/512),(1215/1024)),((2025/512),(4455/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3178_ok T3179_ok
def T3176 : Node := Node.split 2 T3177 T3190
theorem T3176_ok : Node.check D_R22222 T3176 [((163/256),(163/128)),((405/512),(1215/1024)),((2025/512),(1215/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3177_ok T3190_ok
def T3175 : Node := Node.split 1 T3176 T3191
theorem T3175_ok : Node.check D_R22222 T3175 [((163/256),(163/128)),((405/512),(405/256)),((2025/512),(1215/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3176_ok T3191_ok
def T3174 : Node := Node.leaf L3174
theorem T3174_ok : Node.check D_R22222 T3174 [((163/256),(163/128)),((405/512),(405/256)),((2025/512),(1215/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3174_ok
def T3173 : Node := Node.split 3 T3174 T3175
theorem T3173_ok : Node.check D_R22222 T3173 [((163/256),(163/128)),((405/512),(405/256)),((2025/512),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3174_ok T3175_ok
def T3172 : Node := Node.leaf L3172
theorem T3172_ok : Node.check D_R22222 T3172 [((0),(163/256)),((405/512),(405/256)),((2025/512),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3172_ok
def T3171 : Node := Node.split 0 T3172 T3173
theorem T3171_ok : Node.check D_R22222 T3171 [((0),(163/128)),((405/512),(405/256)),((2025/512),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3172_ok T3173_ok
def T3170 : Node := Node.leaf L3170
theorem T3170_ok : Node.check D_R22222 T3170 [((163/256),(163/128)),((1215/1024),(405/256)),((405/128),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3170_ok
def T3169 : Node := Node.leaf L3169
theorem T3169_ok : Node.check D_R22222 T3169 [((489/512),(163/128)),((2025/2048),(1215/1024)),((7695/2048),(2025/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3169_ok
def T3168 : Node := Node.leaf L3168
theorem T3168_ok : Node.check D_R22222 T3168 [((489/512),(163/128)),((2025/2048),(1215/1024)),((3645/1024),(7695/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3168_ok
def T3167 : Node := Node.split 2 T3168 T3169
theorem T3167_ok : Node.check D_R22222 T3167 [((489/512),(163/128)),((2025/2048),(1215/1024)),((3645/1024),(2025/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3168_ok T3169_ok
def T3166 : Node := Node.leaf L3166
theorem T3166_ok : Node.check D_R22222 T3166 [((489/512),(163/128)),((405/512),(2025/2048)),((3645/1024),(2025/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L3166_ok
def T3165 : Node := Node.split 1 T3166 T3167
theorem T3165_ok : Node.check D_R22222 T3165 [((489/512),(163/128)),((405/512),(1215/1024)),((3645/1024),(2025/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3166_ok T3167_ok
def T3164 : Node := Node.leaf L3164
theorem T3164_ok : Node.check D_R22222 T3164 [((489/512),(163/128)),((405/512),(1215/1024)),((3645/1024),(2025/512)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L3164_ok
def T3163 : Node := Node.split 3 T3164 T3165
theorem T3163_ok : Node.check D_R22222 T3163 [((489/512),(163/128)),((405/512),(1215/1024)),((3645/1024),(2025/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3164_ok T3165_ok
def T3162 : Node := Node.leaf L3162
theorem T3162_ok : Node.check D_R22222 T3162 [((163/256),(489/512)),((405/512),(1215/1024)),((3645/1024),(2025/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3162_ok
def T3161 : Node := Node.split 0 T3162 T3163
theorem T3161_ok : Node.check D_R22222 T3161 [((163/256),(163/128)),((405/512),(1215/1024)),((3645/1024),(2025/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3162_ok T3163_ok
def T3160 : Node := Node.leaf L3160
theorem T3160_ok : Node.check D_R22222 T3160 [((163/256),(163/128)),((405/512),(1215/1024)),((405/128),(3645/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L3160_ok
def T3159 : Node := Node.split 2 T3160 T3161
theorem T3159_ok : Node.check D_R22222 T3159 [((163/256),(163/128)),((405/512),(1215/1024)),((405/128),(2025/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3160_ok T3161_ok
def T3158 : Node := Node.split 1 T3159 T3170
theorem T3158_ok : Node.check D_R22222 T3158 [((163/256),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3159_ok T3170_ok
def T3157 : Node := Node.leaf L3157
theorem T3157_ok : Node.check D_R22222 T3157 [((163/256),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L3157_ok
def T3156 : Node := Node.split 3 T3157 T3158
theorem T3156_ok : Node.check D_R22222 T3156 [((163/256),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3157_ok T3158_ok
def T3155 : Node := Node.leaf L3155
theorem T3155_ok : Node.check D_R22222 T3155 [((0),(163/256)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3155_ok
def T3154 : Node := Node.split 0 T3155 T3156
theorem T3154_ok : Node.check D_R22222 T3154 [((0),(163/128)),((405/512),(405/256)),((405/128),(2025/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3155_ok T3156_ok
def T3153 : Node := Node.split 2 T3154 T3171
theorem T3153_ok : Node.check D_R22222 T3153 [((0),(163/128)),((405/512),(405/256)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3154_ok T3171_ok
def T3152 : Node := Node.leaf L3152
theorem T3152_ok : Node.check D_R22222 T3152 [((0),(163/128)),((0),(405/512)),((405/128),(1215/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L3152_ok
def T3151 : Node := Node.split 1 T3152 T3153
theorem T3151_ok : Node.check D_R22222 T3151 [((0),(163/128)),((0),(405/256)),((405/128),(1215/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3152_ok T3153_ok
def T3150 : Node := Node.split 3 T3151 T3192
theorem T3150_ok : Node.check D_R22222 T3150 [((0),(163/128)),((0),(405/256)),((405/128),(1215/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3151_ok T3192_ok
def T3149 : Node := Node.split 0 T3150 T3209
theorem T3149_ok : Node.check D_R22222 T3149 [((0),(163/64)),((0),(405/256)),((405/128),(1215/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3150_ok T3209_ok
def T3148 : Node := Node.split 2 T3149 T3240
theorem T3148_ok : Node.check D_R22222 T3148 [((0),(163/64)),((0),(405/256)),((405/128),(405/64)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3149_ok T3240_ok
def T3147 : Node := Node.split 1 T3148 T3259
theorem T3147_ok : Node.check D_R22222 T3147 [((0),(163/64)),((0),(405/128)),((405/128),(405/64)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3148_ok T3259_ok
def T3146 : Node := Node.split 3 T3147 T3306
theorem T3146_ok : Node.check D_R22222 T3146 [((0),(163/64)),((0),(405/128)),((405/128),(405/64)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3147_ok T3306_ok
def T3145 : Node := Node.split 0 T3146 T3329
theorem T3145_ok : Node.check D_R22222 T3145 [((0),(163/32)),((0),(405/128)),((405/128),(405/64)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3146_ok T3329_ok
def T3144 : Node := Node.leaf L3144
theorem T3144_ok : Node.check D_R22222 T3144 [((163/64),(163/32)),((405/256),(405/128)),((405/256),(405/128)),((163/64),(163/32))] = true := Node.check_leaf_of _ _ _ L3144_ok
def T3143 : Node := Node.leaf L3143
theorem T3143_ok : Node.check D_R22222 T3143 [((489/128),(163/32)),((405/256),(405/128)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3143_ok
def T3142 : Node := Node.leaf L3142
theorem T3142_ok : Node.check D_R22222 T3142 [((489/128),(163/32)),((1215/512),(405/128)),((0),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3142_ok
def T3141 : Node := Node.leaf L3141
theorem T3141_ok : Node.check D_R22222 T3141 [((489/128),(163/32)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3141_ok
def T3140 : Node := Node.leaf L3140
theorem T3140_ok : Node.check D_R22222 T3140 [((489/128),(163/32)),((405/256),(1215/512)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3140_ok
def T3139 : Node := Node.split 2 T3140 T3141
theorem T3139_ok : Node.check D_R22222 T3139 [((489/128),(163/32)),((405/256),(1215/512)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3140_ok T3141_ok
def T3138 : Node := Node.split 1 T3139 T3142
theorem T3138_ok : Node.check D_R22222 T3138 [((489/128),(163/32)),((405/256),(405/128)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3139_ok T3142_ok
def T3137 : Node := Node.split 3 T3138 T3143
theorem T3137_ok : Node.check D_R22222 T3137 [((489/128),(163/32)),((405/256),(405/128)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3138_ok T3143_ok
def T3136 : Node := Node.leaf L3136
theorem T3136_ok : Node.check D_R22222 T3136 [((163/64),(489/128)),((1215/512),(405/128)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3136_ok
def T3135 : Node := Node.leaf L3135
theorem T3135_ok : Node.check D_R22222 T3135 [((163/64),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3135_ok
def T3134 : Node := Node.leaf L3134
theorem T3134_ok : Node.check D_R22222 T3134 [((163/64),(489/128)),((405/256),(1215/512)),((0),(405/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3134_ok
def T3133 : Node := Node.split 2 T3134 T3135
theorem T3133_ok : Node.check D_R22222 T3133 [((163/64),(489/128)),((405/256),(1215/512)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3134_ok T3135_ok
def T3132 : Node := Node.split 1 T3133 T3136
theorem T3132_ok : Node.check D_R22222 T3132 [((163/64),(489/128)),((405/256),(405/128)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3133_ok T3136_ok
def T3131 : Node := Node.leaf L3131
theorem T3131_ok : Node.check D_R22222 T3131 [((163/64),(489/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3131_ok
def T3130 : Node := Node.leaf L3130
theorem T3130_ok : Node.check D_R22222 T3130 [((163/64),(489/128)),((1215/512),(405/128)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3130_ok
def T3129 : Node := Node.split 2 T3130 T3131
theorem T3129_ok : Node.check D_R22222 T3129 [((163/64),(489/128)),((1215/512),(405/128)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3130_ok T3131_ok
def T3128 : Node := Node.leaf L3128
theorem T3128_ok : Node.check D_R22222 T3128 [((815/256),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3128_ok
def T3127 : Node := Node.leaf L3127
theorem T3127_ok : Node.check D_R22222 T3127 [((163/64),(815/256)),((405/256),(1215/512)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L3127_ok
def T3126 : Node := Node.leaf L3126
theorem T3126_ok : Node.check D_R22222 T3126 [((163/64),(815/256)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3126_ok
def T3125 : Node := Node.leaf L3125
theorem T3125_ok : Node.check D_R22222 T3125 [((163/64),(815/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3125_ok
def T3124 : Node := Node.split 2 T3125 T3126
theorem T3124_ok : Node.check D_R22222 T3124 [((163/64),(815/256)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3125_ok T3126_ok
def T3123 : Node := Node.leaf L3123
theorem T3123_ok : Node.check D_R22222 T3123 [((163/64),(815/256)),((405/256),(2025/1024)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3123_ok
def T3122 : Node := Node.split 1 T3123 T3124
theorem T3122_ok : Node.check D_R22222 T3122 [((163/64),(815/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3123_ok T3124_ok
def T3121 : Node := Node.split 3 T3122 T3127
theorem T3121_ok : Node.check D_R22222 T3121 [((163/64),(815/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3122_ok T3127_ok
def T3120 : Node := Node.split 0 T3121 T3128
theorem T3120_ok : Node.check D_R22222 T3120 [((163/64),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3121_ok T3128_ok
def T3119 : Node := Node.leaf L3119
theorem T3119_ok : Node.check D_R22222 T3119 [((163/64),(489/128)),((405/256),(1215/512)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3119_ok
def T3118 : Node := Node.split 2 T3119 T3120
theorem T3118_ok : Node.check D_R22222 T3118 [((163/64),(489/128)),((405/256),(1215/512)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3119_ok T3120_ok
def T3117 : Node := Node.split 1 T3118 T3129
theorem T3117_ok : Node.check D_R22222 T3117 [((163/64),(489/128)),((405/256),(405/128)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3118_ok T3129_ok
def T3116 : Node := Node.split 3 T3117 T3132
theorem T3116_ok : Node.check D_R22222 T3116 [((163/64),(489/128)),((405/256),(405/128)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3117_ok T3132_ok
def T3115 : Node := Node.split 0 T3116 T3137
theorem T3115_ok : Node.check D_R22222 T3115 [((163/64),(163/32)),((405/256),(405/128)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3116_ok T3137_ok
def T3114 : Node := Node.split 2 T3115 T3144
theorem T3114_ok : Node.check D_R22222 T3114 [((163/64),(163/32)),((405/256),(405/128)),((0),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3115_ok T3144_ok
def T3113 : Node := Node.leaf L3113
theorem T3113_ok : Node.check D_R22222 T3113 [((489/128),(163/32)),((0),(405/256)),((405/256),(405/128)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3113_ok
def T3112 : Node := Node.leaf L3112
theorem T3112_ok : Node.check D_R22222 T3112 [((489/128),(163/32)),((405/512),(405/256)),((405/256),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3112_ok
def T3111 : Node := Node.leaf L3111
theorem T3111_ok : Node.check D_R22222 T3111 [((489/128),(163/32)),((0),(405/512)),((405/256),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3111_ok
def T3110 : Node := Node.split 1 T3111 T3112
theorem T3110_ok : Node.check D_R22222 T3110 [((489/128),(163/32)),((0),(405/256)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3111_ok T3112_ok
def T3109 : Node := Node.split 3 T3110 T3113
theorem T3109_ok : Node.check D_R22222 T3109 [((489/128),(163/32)),((0),(405/256)),((405/256),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3110_ok T3113_ok
def T3108 : Node := Node.leaf L3108
theorem T3108_ok : Node.check D_R22222 T3108 [((163/64),(489/128)),((405/512),(405/256)),((405/256),(405/128)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3108_ok
def T3107 : Node := Node.leaf L3107
theorem T3107_ok : Node.check D_R22222 T3107 [((163/64),(489/128)),((0),(405/512)),((405/256),(405/128)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3107_ok
def T3106 : Node := Node.split 1 T3107 T3108
theorem T3106_ok : Node.check D_R22222 T3106 [((163/64),(489/128)),((0),(405/256)),((405/256),(405/128)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3107_ok T3108_ok
def T3105 : Node := Node.leaf L3105
theorem T3105_ok : Node.check D_R22222 T3105 [((163/64),(489/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3105_ok
def T3104 : Node := Node.leaf L3104
theorem T3104_ok : Node.check D_R22222 T3104 [((815/256),(489/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3104_ok
def T3103 : Node := Node.leaf L3103
theorem T3103_ok : Node.check D_R22222 T3103 [((163/64),(815/256)),((405/512),(405/256)),((405/256),(1215/512)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L3103_ok
def T3102 : Node := Node.leaf L3102
theorem T3102_ok : Node.check D_R22222 T3102 [((163/64),(815/256)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3102_ok
def T3101 : Node := Node.leaf L3101
theorem T3101_ok : Node.check D_R22222 T3101 [((163/64),(815/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3101_ok
def T3100 : Node := Node.leaf L3100
theorem T3100_ok : Node.check D_R22222 T3100 [((163/64),(815/256)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3100_ok
def T3099 : Node := Node.split 2 T3100 T3101
theorem T3099_ok : Node.check D_R22222 T3099 [((163/64),(815/256)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3100_ok T3101_ok
def T3098 : Node := Node.split 1 T3099 T3102
theorem T3098_ok : Node.check D_R22222 T3098 [((163/64),(815/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3099_ok T3102_ok
def T3097 : Node := Node.split 3 T3098 T3103
theorem T3097_ok : Node.check D_R22222 T3097 [((163/64),(815/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3098_ok T3103_ok
def T3096 : Node := Node.split 0 T3097 T3104
theorem T3096_ok : Node.check D_R22222 T3096 [((163/64),(489/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3097_ok T3104_ok
def T3095 : Node := Node.split 2 T3096 T3105
theorem T3095_ok : Node.check D_R22222 T3095 [((163/64),(489/128)),((405/512),(405/256)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3096_ok T3105_ok
def T3094 : Node := Node.leaf L3094
theorem T3094_ok : Node.check D_R22222 T3094 [((163/64),(489/128)),((0),(405/512)),((405/256),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3094_ok
def T3093 : Node := Node.split 1 T3094 T3095
theorem T3093_ok : Node.check D_R22222 T3093 [((163/64),(489/128)),((0),(405/256)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3094_ok T3095_ok
def T3092 : Node := Node.split 3 T3093 T3106
theorem T3092_ok : Node.check D_R22222 T3092 [((163/64),(489/128)),((0),(405/256)),((405/256),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3093_ok T3106_ok
def T3091 : Node := Node.split 0 T3092 T3109
theorem T3091_ok : Node.check D_R22222 T3091 [((163/64),(163/32)),((0),(405/256)),((405/256),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3092_ok T3109_ok
def T3090 : Node := Node.leaf L3090
theorem T3090_ok : Node.check D_R22222 T3090 [((489/128),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3090_ok
def T3089 : Node := Node.leaf L3089
theorem T3089_ok : Node.check D_R22222 T3089 [((489/128),(163/32)),((405/512),(405/256)),((0),(405/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3089_ok
def T3088 : Node := Node.split 2 T3089 T3090
theorem T3088_ok : Node.check D_R22222 T3088 [((489/128),(163/32)),((405/512),(405/256)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3089_ok T3090_ok
def T3087 : Node := Node.leaf L3087
theorem T3087_ok : Node.check D_R22222 T3087 [((489/128),(163/32)),((0),(405/512)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3087_ok
def T3086 : Node := Node.split 1 T3087 T3088
theorem T3086_ok : Node.check D_R22222 T3086 [((489/128),(163/32)),((0),(405/256)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3087_ok T3088_ok
def T3085 : Node := Node.leaf L3085
theorem T3085_ok : Node.check D_R22222 T3085 [((1141/256),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L3085_ok
def T3084 : Node := Node.leaf L3084
theorem T3084_ok : Node.check D_R22222 T3084 [((1141/256),(163/32)),((1215/1024),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3084_ok
def T3083 : Node := Node.leaf L3083
theorem T3083_ok : Node.check D_R22222 T3083 [((1141/256),(163/32)),((405/512),(1215/1024)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3083_ok
def T3082 : Node := Node.split 1 T3083 T3084
theorem T3082_ok : Node.check D_R22222 T3082 [((1141/256),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3083_ok T3084_ok
def T3081 : Node := Node.split 3 T3082 T3085
theorem T3081_ok : Node.check D_R22222 T3081 [((1141/256),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3082_ok T3085_ok
def T3080 : Node := Node.leaf L3080
theorem T3080_ok : Node.check D_R22222 T3080 [((489/128),(1141/256)),((405/512),(405/256)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L3080_ok
def T3079 : Node := Node.leaf L3079
theorem T3079_ok : Node.check D_R22222 T3079 [((489/128),(1141/256)),((1215/1024),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3079_ok
def T3078 : Node := Node.leaf L3078
theorem T3078_ok : Node.check D_R22222 T3078 [((489/128),(1141/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3078_ok
def T3077 : Node := Node.leaf L3077
theorem T3077_ok : Node.check D_R22222 T3077 [((2119/512),(1141/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3077_ok
def T3076 : Node := Node.leaf L3076
theorem T3076_ok : Node.check D_R22222 T3076 [((489/128),(2119/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L3076_ok
def T3075 : Node := Node.leaf L3075
theorem T3075_ok : Node.check D_R22222 T3075 [((489/128),(2119/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L3075_ok
def T3074 : Node := Node.split 3 T3075 T3076
theorem T3074_ok : Node.check D_R22222 T3074 [((489/128),(2119/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3075_ok T3076_ok
def T3073 : Node := Node.split 0 T3074 T3077
theorem T3073_ok : Node.check D_R22222 T3073 [((489/128),(1141/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3074_ok T3077_ok
def T3072 : Node := Node.split 2 T3073 T3078
theorem T3072_ok : Node.check D_R22222 T3072 [((489/128),(1141/256)),((405/512),(1215/1024)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3073_ok T3078_ok
def T3071 : Node := Node.split 1 T3072 T3079
theorem T3071_ok : Node.check D_R22222 T3071 [((489/128),(1141/256)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3072_ok T3079_ok
def T3070 : Node := Node.split 3 T3071 T3080
theorem T3070_ok : Node.check D_R22222 T3070 [((489/128),(1141/256)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3071_ok T3080_ok
def T3069 : Node := Node.split 0 T3070 T3081
theorem T3069_ok : Node.check D_R22222 T3069 [((489/128),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3070_ok T3081_ok
def T3068 : Node := Node.leaf L3068
theorem T3068_ok : Node.check D_R22222 T3068 [((489/128),(163/32)),((405/512),(405/256)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3068_ok
def T3067 : Node := Node.split 2 T3068 T3069
theorem T3067_ok : Node.check D_R22222 T3067 [((489/128),(163/32)),((405/512),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3068_ok T3069_ok
def T3066 : Node := Node.leaf L3066
theorem T3066_ok : Node.check D_R22222 T3066 [((489/128),(163/32)),((0),(405/512)),((0),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L3066_ok
def T3065 : Node := Node.split 1 T3066 T3067
theorem T3065_ok : Node.check D_R22222 T3065 [((489/128),(163/32)),((0),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3066_ok T3067_ok
def T3064 : Node := Node.split 3 T3065 T3086
theorem T3064_ok : Node.check D_R22222 T3064 [((489/128),(163/32)),((0),(405/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3065_ok T3086_ok
def T3063 : Node := Node.leaf L3063
theorem T3063_ok : Node.check D_R22222 T3063 [((815/256),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3063_ok
def T3062 : Node := Node.leaf L3062
theorem T3062_ok : Node.check D_R22222 T3062 [((163/64),(815/256)),((1215/1024),(405/256)),((405/512),(405/256)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L3062_ok
def T3061 : Node := Node.leaf L3061
theorem T3061_ok : Node.check D_R22222 T3061 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(405/256)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L3061_ok
def T3060 : Node := Node.split 1 T3061 T3062
theorem T3060_ok : Node.check D_R22222 T3060 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3061_ok T3062_ok
def T3059 : Node := Node.leaf L3059
theorem T3059_ok : Node.check D_R22222 T3059 [((163/64),(815/256)),((1215/1024),(405/256)),((405/512),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L3059_ok
def T3058 : Node := Node.leaf L3058
theorem T3058_ok : Node.check D_R22222 T3058 [((163/64),(815/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L3058_ok
def T3057 : Node := Node.leaf L3057
theorem T3057_ok : Node.check D_R22222 T3057 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L3057_ok
def T3056 : Node := Node.leaf L3056
theorem T3056_ok : Node.check D_R22222 T3056 [((163/64),(1467/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L3056_ok
def T3055 : Node := Node.split 0 T3056 T3057
theorem T3055_ok : Node.check D_R22222 T3055 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3056_ok T3057_ok
def T3054 : Node := Node.split 2 T3055 T3058
theorem T3054_ok : Node.check D_R22222 T3054 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3055_ok T3058_ok
def T3053 : Node := Node.split 1 T3054 T3059
theorem T3053_ok : Node.check D_R22222 T3053 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3054_ok T3059_ok
def T3052 : Node := Node.split 3 T3053 T3060
theorem T3052_ok : Node.check D_R22222 T3052 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3053_ok T3060_ok
def T3051 : Node := Node.split 0 T3052 T3063
theorem T3051_ok : Node.check D_R22222 T3051 [((163/64),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3052_ok T3063_ok
def T3050 : Node := Node.leaf L3050
theorem T3050_ok : Node.check D_R22222 T3050 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3050_ok
def T3049 : Node := Node.split 2 T3050 T3051
theorem T3049_ok : Node.check D_R22222 T3049 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3050_ok T3051_ok
def T3048 : Node := Node.leaf L3048
theorem T3048_ok : Node.check D_R22222 T3048 [((163/64),(489/128)),((0),(405/512)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L3048_ok
def T3047 : Node := Node.split 1 T3048 T3049
theorem T3047_ok : Node.check D_R22222 T3047 [((163/64),(489/128)),((0),(405/256)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3048_ok T3049_ok
def T3046 : Node := Node.leaf L3046
theorem T3046_ok : Node.check D_R22222 T3046 [((815/256),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L3046_ok
def T3045 : Node := Node.leaf L3045
theorem T3045_ok : Node.check D_R22222 T3045 [((815/256),(489/128)),((1215/1024),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3045_ok
def T3044 : Node := Node.leaf L3044
theorem T3044_ok : Node.check D_R22222 T3044 [((815/256),(489/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3044_ok
def T3043 : Node := Node.leaf L3043
theorem T3043_ok : Node.check D_R22222 T3043 [((815/256),(489/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3043_ok
def T3042 : Node := Node.split 2 T3043 T3044
theorem T3042_ok : Node.check D_R22222 T3042 [((815/256),(489/128)),((405/512),(1215/1024)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3043_ok T3044_ok
def T3041 : Node := Node.split 1 T3042 T3045
theorem T3041_ok : Node.check D_R22222 T3041 [((815/256),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3042_ok T3045_ok
def T3040 : Node := Node.split 3 T3041 T3046
theorem T3040_ok : Node.check D_R22222 T3040 [((815/256),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3041_ok T3046_ok
def T3039 : Node := Node.leaf L3039
theorem T3039_ok : Node.check D_R22222 T3039 [((163/64),(815/256)),((1215/1024),(405/256)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L3039_ok
def T3038 : Node := Node.leaf L3038
theorem T3038_ok : Node.check D_R22222 T3038 [((163/64),(815/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L3038_ok
def T3037 : Node := Node.leaf L3037
theorem T3037_ok : Node.check D_R22222 T3037 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L3037_ok
def T3036 : Node := Node.split 2 T3037 T3038
theorem T3036_ok : Node.check D_R22222 T3036 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(405/256)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3037_ok T3038_ok
def T3035 : Node := Node.split 1 T3036 T3039
theorem T3035_ok : Node.check D_R22222 T3035 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3036_ok T3039_ok
def T3034 : Node := Node.leaf L3034
theorem T3034_ok : Node.check D_R22222 T3034 [((163/64),(815/256)),((1215/1024),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3034_ok
def T3033 : Node := Node.leaf L3033
theorem T3033_ok : Node.check D_R22222 T3033 [((163/64),(815/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3033_ok
def T3032 : Node := Node.leaf L3032
theorem T3032_ok : Node.check D_R22222 T3032 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L3032_ok
def T3031 : Node := Node.leaf L3031
theorem T3031_ok : Node.check D_R22222 T3031 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L3031_ok
def T3030 : Node := Node.leaf L3030
theorem T3030_ok : Node.check D_R22222 T3030 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L3030_ok
def T3029 : Node := Node.split 2 T3030 T3031
theorem T3029_ok : Node.check D_R22222 T3029 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3030_ok T3031_ok
def T3028 : Node := Node.split 1 T3029 T3032
theorem T3028_ok : Node.check D_R22222 T3028 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3029_ok T3032_ok
def T3027 : Node := Node.leaf L3027
theorem T3027_ok : Node.check D_R22222 T3027 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L3027_ok
def T3026 : Node := Node.leaf L3026
theorem T3026_ok : Node.check D_R22222 T3026 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L3026_ok
def T3025 : Node := Node.leaf L3025
theorem T3025_ok : Node.check D_R22222 T3025 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L3025_ok
def T3024 : Node := Node.split 2 T3025 T3026
theorem T3024_ok : Node.check D_R22222 T3024 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3025_ok T3026_ok
def T3023 : Node := Node.split 1 T3024 T3027
theorem T3023_ok : Node.check D_R22222 T3023 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3024_ok T3027_ok
def T3022 : Node := Node.split 3 T3023 T3028
theorem T3022_ok : Node.check D_R22222 T3022 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3023_ok T3028_ok
def T3021 : Node := Node.leaf L3021
theorem T3021_ok : Node.check D_R22222 T3021 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L3021_ok
def T3020 : Node := Node.leaf L3020
theorem T3020_ok : Node.check D_R22222 T3020 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L3020_ok
def T3019 : Node := Node.leaf L3019
theorem T3019_ok : Node.check D_R22222 T3019 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L3019_ok
def T3018 : Node := Node.split 2 T3019 T3020
theorem T3018_ok : Node.check D_R22222 T3018 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3019_ok T3020_ok
def T3017 : Node := Node.split 1 T3018 T3021
theorem T3017_ok : Node.check D_R22222 T3017 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3018_ok T3021_ok
def T3016 : Node := Node.leaf L3016
theorem T3016_ok : Node.check D_R22222 T3016 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L3016_ok
def T3015 : Node := Node.leaf L3015
theorem T3015_ok : Node.check D_R22222 T3015 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L3015_ok
def T3014 : Node := Node.split 2 T3015 T3016
theorem T3014_ok : Node.check D_R22222 T3014 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3015_ok T3016_ok
def T3013 : Node := Node.leaf L3013
theorem T3013_ok : Node.check D_R22222 T3013 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L3013_ok
def T3012 : Node := Node.split 1 T3013 T3014
theorem T3012_ok : Node.check D_R22222 T3012 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3013_ok T3014_ok
def T3011 : Node := Node.split 3 T3012 T3017
theorem T3011_ok : Node.check D_R22222 T3011 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3012_ok T3017_ok
def T3010 : Node := Node.split 0 T3011 T3022
theorem T3010_ok : Node.check D_R22222 T3010 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3011_ok T3022_ok
def T3009 : Node := Node.leaf L3009
theorem T3009_ok : Node.check D_R22222 T3009 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L3009_ok
def T3008 : Node := Node.split 2 T3009 T3010
theorem T3008_ok : Node.check D_R22222 T3008 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3009_ok T3010_ok
def T3007 : Node := Node.leaf L3007
theorem T3007_ok : Node.check D_R22222 T3007 [((1467/512),(815/256)),((405/512),(2025/2048)),((405/512),(1215/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L3007_ok
def T3006 : Node := Node.split 1 T3007 T3008
theorem T3006_ok : Node.check D_R22222 T3006 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3007_ok T3008_ok
def T3005 : Node := Node.leaf L3005
theorem T3005_ok : Node.check D_R22222 T3005 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L3005_ok
def T3004 : Node := Node.split 3 T3005 T3006
theorem T3004_ok : Node.check D_R22222 T3004 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3005_ok T3006_ok
def T3003 : Node := Node.leaf L3003
theorem T3003_ok : Node.check D_R22222 T3003 [((163/64),(1467/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L3003_ok
def T3002 : Node := Node.split 0 T3003 T3004
theorem T3002_ok : Node.check D_R22222 T3002 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3003_ok T3004_ok
def T3001 : Node := Node.split 2 T3002 T3033
theorem T3001_ok : Node.check D_R22222 T3001 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3002_ok T3033_ok
def T3000 : Node := Node.split 1 T3001 T3034
theorem T3000_ok : Node.check D_R22222 T3000 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3001_ok T3034_ok
def T2999 : Node := Node.split 3 T3000 T3035
theorem T2999_ok : Node.check D_R22222 T2999 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3000_ok T3035_ok
def T2998 : Node := Node.split 0 T2999 T3040
theorem T2998_ok : Node.check D_R22222 T2998 [((163/64),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2999_ok T3040_ok
def T2997 : Node := Node.leaf L2997
theorem T2997_ok : Node.check D_R22222 T2997 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2997_ok
def T2996 : Node := Node.split 2 T2997 T2998
theorem T2996_ok : Node.check D_R22222 T2996 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2997_ok T2998_ok
def T2995 : Node := Node.leaf L2995
theorem T2995_ok : Node.check D_R22222 T2995 [((163/64),(489/128)),((0),(405/512)),((0),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2995_ok
def T2994 : Node := Node.split 1 T2995 T2996
theorem T2994_ok : Node.check D_R22222 T2994 [((163/64),(489/128)),((0),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2995_ok T2996_ok
def T2993 : Node := Node.split 3 T2994 T3047
theorem T2993_ok : Node.check D_R22222 T2993 [((163/64),(489/128)),((0),(405/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2994_ok T3047_ok
def T2992 : Node := Node.split 0 T2993 T3064
theorem T2992_ok : Node.check D_R22222 T2992 [((163/64),(163/32)),((0),(405/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2993_ok T3064_ok
def T2991 : Node := Node.split 2 T2992 T3091
theorem T2991_ok : Node.check D_R22222 T2991 [((163/64),(163/32)),((0),(405/256)),((0),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2992_ok T3091_ok
def T2990 : Node := Node.split 1 T2991 T3114
theorem T2990_ok : Node.check D_R22222 T2990 [((163/64),(163/32)),((0),(405/128)),((0),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2991_ok T3114_ok
def T2989 : Node := Node.leaf L2989
theorem T2989_ok : Node.check D_R22222 T2989 [((489/128),(163/32)),((405/256),(405/128)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2989_ok
def T2988 : Node := Node.leaf L2988
theorem T2988_ok : Node.check D_R22222 T2988 [((489/128),(163/32)),((1215/512),(405/128)),((405/256),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2988_ok
def T2987 : Node := Node.leaf L2987
theorem T2987_ok : Node.check D_R22222 T2987 [((489/128),(163/32)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2987_ok
def T2986 : Node := Node.leaf L2986
theorem T2986_ok : Node.check D_R22222 T2986 [((1141/256),(163/32)),((405/256),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2986_ok
def T2985 : Node := Node.leaf L2985
theorem T2985_ok : Node.check D_R22222 T2985 [((1141/256),(163/32)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2985_ok
def T2984 : Node := Node.split 3 T2985 T2986
theorem T2984_ok : Node.check D_R22222 T2984 [((1141/256),(163/32)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2985_ok T2986_ok
def T2983 : Node := Node.leaf L2983
theorem T2983_ok : Node.check D_R22222 T2983 [((489/128),(1141/256)),((2025/1024),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2983_ok
def T2982 : Node := Node.leaf L2982
theorem T2982_ok : Node.check D_R22222 T2982 [((489/128),(1141/256)),((405/256),(2025/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2982_ok
def T2981 : Node := Node.split 1 T2982 T2983
theorem T2981_ok : Node.check D_R22222 T2981 [((489/128),(1141/256)),((405/256),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2982_ok T2983_ok
def T2980 : Node := Node.leaf L2980
theorem T2980_ok : Node.check D_R22222 T2980 [((489/128),(1141/256)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2980_ok
def T2979 : Node := Node.split 3 T2980 T2981
theorem T2979_ok : Node.check D_R22222 T2979 [((489/128),(1141/256)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2980_ok T2981_ok
def T2978 : Node := Node.split 0 T2979 T2984
theorem T2978_ok : Node.check D_R22222 T2978 [((489/128),(163/32)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2979_ok T2984_ok
def T2977 : Node := Node.split 2 T2978 T2987
theorem T2977_ok : Node.check D_R22222 T2977 [((489/128),(163/32)),((405/256),(1215/512)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2978_ok T2987_ok
def T2976 : Node := Node.split 1 T2977 T2988
theorem T2976_ok : Node.check D_R22222 T2976 [((489/128),(163/32)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2977_ok T2988_ok
def T2975 : Node := Node.split 3 T2976 T2989
theorem T2975_ok : Node.check D_R22222 T2975 [((489/128),(163/32)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2976_ok T2989_ok
def T2974 : Node := Node.leaf L2974
theorem T2974_ok : Node.check D_R22222 T2974 [((163/64),(489/128)),((1215/512),(405/128)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2974_ok
def T2973 : Node := Node.leaf L2973
theorem T2973_ok : Node.check D_R22222 T2973 [((163/64),(489/128)),((405/256),(1215/512)),((1215/512),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2973_ok
def T2972 : Node := Node.leaf L2972
theorem T2972_ok : Node.check D_R22222 T2972 [((815/256),(489/128)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2972_ok
def T2971 : Node := Node.leaf L2971
theorem T2971_ok : Node.check D_R22222 T2971 [((163/64),(815/256)),((2025/1024),(1215/512)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2971_ok
def T2970 : Node := Node.leaf L2970
theorem T2970_ok : Node.check D_R22222 T2970 [((163/64),(815/256)),((405/256),(2025/1024)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2970_ok
def T2969 : Node := Node.split 1 T2970 T2971
theorem T2969_ok : Node.check D_R22222 T2969 [((163/64),(815/256)),((405/256),(1215/512)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2970_ok T2971_ok
def T2968 : Node := Node.leaf L2968
theorem T2968_ok : Node.check D_R22222 T2968 [((163/64),(815/256)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2968_ok
def T2967 : Node := Node.split 3 T2968 T2969
theorem T2967_ok : Node.check D_R22222 T2967 [((163/64),(815/256)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2968_ok T2969_ok
def T2966 : Node := Node.split 0 T2967 T2972
theorem T2966_ok : Node.check D_R22222 T2966 [((163/64),(489/128)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2967_ok T2972_ok
def T2965 : Node := Node.split 2 T2966 T2973
theorem T2965_ok : Node.check D_R22222 T2965 [((163/64),(489/128)),((405/256),(1215/512)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2966_ok T2973_ok
def T2964 : Node := Node.split 1 T2965 T2974
theorem T2964_ok : Node.check D_R22222 T2964 [((163/64),(489/128)),((405/256),(405/128)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2965_ok T2974_ok
def T2963 : Node := Node.leaf L2963
theorem T2963_ok : Node.check D_R22222 T2963 [((163/64),(489/128)),((1215/512),(405/128)),((1215/512),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2963_ok
def T2962 : Node := Node.leaf L2962
theorem T2962_ok : Node.check D_R22222 T2962 [((815/256),(489/128)),((1215/512),(405/128)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2962_ok
def T2961 : Node := Node.leaf L2961
theorem T2961_ok : Node.check D_R22222 T2961 [((815/256),(489/128)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2961_ok
def T2960 : Node := Node.split 3 T2961 T2962
theorem T2960_ok : Node.check D_R22222 T2960 [((815/256),(489/128)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2961_ok T2962_ok
def T2959 : Node := Node.leaf L2959
theorem T2959_ok : Node.check D_R22222 T2959 [((163/64),(815/256)),((2835/1024),(405/128)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2959_ok
def T2958 : Node := Node.leaf L2958
theorem T2958_ok : Node.check D_R22222 T2958 [((163/64),(815/256)),((1215/512),(2835/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2958_ok
def T2957 : Node := Node.split 1 T2958 T2959
theorem T2957_ok : Node.check D_R22222 T2957 [((163/64),(815/256)),((1215/512),(405/128)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2958_ok T2959_ok
def T2956 : Node := Node.leaf L2956
theorem T2956_ok : Node.check D_R22222 T2956 [((163/64),(815/256)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2956_ok
def T2955 : Node := Node.split 3 T2956 T2957
theorem T2955_ok : Node.check D_R22222 T2955 [((163/64),(815/256)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2956_ok T2957_ok
def T2954 : Node := Node.split 0 T2955 T2960
theorem T2954_ok : Node.check D_R22222 T2954 [((163/64),(489/128)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2955_ok T2960_ok
def T2953 : Node := Node.split 2 T2954 T2963
theorem T2953_ok : Node.check D_R22222 T2953 [((163/64),(489/128)),((1215/512),(405/128)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2954_ok T2963_ok
def T2952 : Node := Node.leaf L2952
theorem T2952_ok : Node.check D_R22222 T2952 [((815/256),(489/128)),((405/256),(1215/512)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2952_ok
def T2951 : Node := Node.leaf L2951
theorem T2951_ok : Node.check D_R22222 T2951 [((815/256),(489/128)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2951_ok
def T2950 : Node := Node.split 3 T2951 T2952
theorem T2950_ok : Node.check D_R22222 T2950 [((815/256),(489/128)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2951_ok T2952_ok
def T2949 : Node := Node.leaf L2949
theorem T2949_ok : Node.check D_R22222 T2949 [((163/64),(815/256)),((2025/1024),(1215/512)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2949_ok
def T2948 : Node := Node.leaf L2948
theorem T2948_ok : Node.check D_R22222 T2948 [((163/64),(815/256)),((405/256),(2025/1024)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2948_ok
def T2947 : Node := Node.split 1 T2948 T2949
theorem T2947_ok : Node.check D_R22222 T2947 [((163/64),(815/256)),((405/256),(1215/512)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2948_ok T2949_ok
def T2946 : Node := Node.leaf L2946
theorem T2946_ok : Node.check D_R22222 T2946 [((163/64),(815/256)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2946_ok
def T2945 : Node := Node.split 3 T2946 T2947
theorem T2945_ok : Node.check D_R22222 T2945 [((163/64),(815/256)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2946_ok T2947_ok
def T2944 : Node := Node.split 0 T2945 T2950
theorem T2944_ok : Node.check D_R22222 T2944 [((163/64),(489/128)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2945_ok T2950_ok
def T2943 : Node := Node.leaf L2943
theorem T2943_ok : Node.check D_R22222 T2943 [((815/256),(489/128)),((405/256),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2943_ok
def T2942 : Node := Node.leaf L2942
theorem T2942_ok : Node.check D_R22222 T2942 [((815/256),(489/128)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2942_ok
def T2941 : Node := Node.split 3 T2942 T2943
theorem T2941_ok : Node.check D_R22222 T2941 [((815/256),(489/128)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2942_ok T2943_ok
def T2940 : Node := Node.leaf L2940
theorem T2940_ok : Node.check D_R22222 T2940 [((1467/512),(815/256)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2940_ok
def T2939 : Node := Node.leaf L2939
theorem T2939_ok : Node.check D_R22222 T2939 [((163/64),(1467/512)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2939_ok
def T2938 : Node := Node.split 0 T2939 T2940
theorem T2938_ok : Node.check D_R22222 T2938 [((163/64),(815/256)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2939_ok T2940_ok
def T2937 : Node := Node.leaf L2937
theorem T2937_ok : Node.check D_R22222 T2937 [((163/64),(815/256)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2937_ok
def T2936 : Node := Node.split 2 T2937 T2938
theorem T2936_ok : Node.check D_R22222 T2936 [((163/64),(815/256)),((2025/1024),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2937_ok T2938_ok
def T2935 : Node := Node.leaf L2935
theorem T2935_ok : Node.check D_R22222 T2935 [((163/64),(815/256)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2935_ok
def T2934 : Node := Node.leaf L2934
theorem T2934_ok : Node.check D_R22222 T2934 [((163/64),(815/256)),((405/256),(2025/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2934_ok
def T2933 : Node := Node.split 2 T2934 T2935
theorem T2933_ok : Node.check D_R22222 T2933 [((163/64),(815/256)),((405/256),(2025/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2934_ok T2935_ok
def T2932 : Node := Node.split 1 T2933 T2936
theorem T2932_ok : Node.check D_R22222 T2932 [((163/64),(815/256)),((405/256),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2933_ok T2936_ok
def T2931 : Node := Node.leaf L2931
theorem T2931_ok : Node.check D_R22222 T2931 [((163/64),(815/256)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2931_ok
def T2930 : Node := Node.split 3 T2931 T2932
theorem T2930_ok : Node.check D_R22222 T2930 [((163/64),(815/256)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2931_ok T2932_ok
def T2929 : Node := Node.split 0 T2930 T2941
theorem T2929_ok : Node.check D_R22222 T2929 [((163/64),(489/128)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2930_ok T2941_ok
def T2928 : Node := Node.split 2 T2929 T2944
theorem T2928_ok : Node.check D_R22222 T2928 [((163/64),(489/128)),((405/256),(1215/512)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2929_ok T2944_ok
def T2927 : Node := Node.split 1 T2928 T2953
theorem T2927_ok : Node.check D_R22222 T2927 [((163/64),(489/128)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2928_ok T2953_ok
def T2926 : Node := Node.split 3 T2927 T2964
theorem T2926_ok : Node.check D_R22222 T2926 [((163/64),(489/128)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2927_ok T2964_ok
def T2925 : Node := Node.split 0 T2926 T2975
theorem T2925_ok : Node.check D_R22222 T2925 [((163/64),(163/32)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2926_ok T2975_ok
def T2924 : Node := Node.leaf L2924
theorem T2924_ok : Node.check D_R22222 T2924 [((489/128),(163/32)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2924_ok
def T2923 : Node := Node.leaf L2923
theorem T2923_ok : Node.check D_R22222 T2923 [((489/128),(163/32)),((1215/512),(405/128)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2923_ok
def T2922 : Node := Node.split 2 T2923 T2924
theorem T2922_ok : Node.check D_R22222 T2922 [((489/128),(163/32)),((1215/512),(405/128)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2923_ok T2924_ok
def T2921 : Node := Node.leaf L2921
theorem T2921_ok : Node.check D_R22222 T2921 [((1141/256),(163/32)),((405/256),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2921_ok
def T2920 : Node := Node.leaf L2920
theorem T2920_ok : Node.check D_R22222 T2920 [((1141/256),(163/32)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2920_ok
def T2919 : Node := Node.split 3 T2920 T2921
theorem T2919_ok : Node.check D_R22222 T2919 [((1141/256),(163/32)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2920_ok T2921_ok
def T2918 : Node := Node.leaf L2918
theorem T2918_ok : Node.check D_R22222 T2918 [((489/128),(1141/256)),((2025/1024),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2918_ok
def T2917 : Node := Node.leaf L2917
theorem T2917_ok : Node.check D_R22222 T2917 [((489/128),(1141/256)),((405/256),(2025/1024)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2917_ok
def T2916 : Node := Node.split 1 T2917 T2918
theorem T2916_ok : Node.check D_R22222 T2916 [((489/128),(1141/256)),((405/256),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2917_ok T2918_ok
def T2915 : Node := Node.leaf L2915
theorem T2915_ok : Node.check D_R22222 T2915 [((489/128),(1141/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2915_ok
def T2914 : Node := Node.split 3 T2915 T2916
theorem T2914_ok : Node.check D_R22222 T2914 [((489/128),(1141/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2915_ok T2916_ok
def T2913 : Node := Node.split 0 T2914 T2919
theorem T2913_ok : Node.check D_R22222 T2913 [((489/128),(163/32)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2914_ok T2919_ok
def T2912 : Node := Node.leaf L2912
theorem T2912_ok : Node.check D_R22222 T2912 [((489/128),(163/32)),((405/256),(1215/512)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2912_ok
def T2911 : Node := Node.split 2 T2912 T2913
theorem T2911_ok : Node.check D_R22222 T2911 [((489/128),(163/32)),((405/256),(1215/512)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2912_ok T2913_ok
def T2910 : Node := Node.split 1 T2911 T2922
theorem T2910_ok : Node.check D_R22222 T2910 [((489/128),(163/32)),((405/256),(405/128)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2911_ok T2922_ok
def T2909 : Node := Node.leaf L2909
theorem T2909_ok : Node.check D_R22222 T2909 [((1141/256),(163/32)),((1215/512),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2909_ok
def T2908 : Node := Node.leaf L2908
theorem T2908_ok : Node.check D_R22222 T2908 [((1141/256),(163/32)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2908_ok
def T2907 : Node := Node.split 3 T2908 T2909
theorem T2907_ok : Node.check D_R22222 T2907 [((1141/256),(163/32)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2908_ok T2909_ok
def T2906 : Node := Node.leaf L2906
theorem T2906_ok : Node.check D_R22222 T2906 [((489/128),(1141/256)),((2835/1024),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2906_ok
def T2905 : Node := Node.leaf L2905
theorem T2905_ok : Node.check D_R22222 T2905 [((489/128),(1141/256)),((1215/512),(2835/1024)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2905_ok
def T2904 : Node := Node.split 1 T2905 T2906
theorem T2904_ok : Node.check D_R22222 T2904 [((489/128),(1141/256)),((1215/512),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2905_ok T2906_ok
def T2903 : Node := Node.leaf L2903
theorem T2903_ok : Node.check D_R22222 T2903 [((489/128),(1141/256)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2903_ok
def T2902 : Node := Node.split 3 T2903 T2904
theorem T2902_ok : Node.check D_R22222 T2902 [((489/128),(1141/256)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2903_ok T2904_ok
def T2901 : Node := Node.split 0 T2902 T2907
theorem T2901_ok : Node.check D_R22222 T2901 [((489/128),(163/32)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2902_ok T2907_ok
def T2900 : Node := Node.leaf L2900
theorem T2900_ok : Node.check D_R22222 T2900 [((489/128),(163/32)),((1215/512),(405/128)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2900_ok
def T2899 : Node := Node.split 2 T2900 T2901
theorem T2899_ok : Node.check D_R22222 T2899 [((489/128),(163/32)),((1215/512),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2900_ok T2901_ok
def T2898 : Node := Node.leaf L2898
theorem T2898_ok : Node.check D_R22222 T2898 [((1141/256),(163/32)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2898_ok
def T2897 : Node := Node.leaf L2897
theorem T2897_ok : Node.check D_R22222 T2897 [((1141/256),(163/32)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2897_ok
def T2896 : Node := Node.split 2 T2897 T2898
theorem T2896_ok : Node.check D_R22222 T2896 [((1141/256),(163/32)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2897_ok T2898_ok
def T2895 : Node := Node.leaf L2895
theorem T2895_ok : Node.check D_R22222 T2895 [((1141/256),(163/32)),((405/256),(2025/1024)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2895_ok
def T2894 : Node := Node.split 1 T2895 T2896
theorem T2894_ok : Node.check D_R22222 T2894 [((1141/256),(163/32)),((405/256),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2895_ok T2896_ok
def T2893 : Node := Node.leaf L2893
theorem T2893_ok : Node.check D_R22222 T2893 [((1141/256),(163/32)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2893_ok
def T2892 : Node := Node.split 3 T2893 T2894
theorem T2892_ok : Node.check D_R22222 T2892 [((1141/256),(163/32)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2893_ok T2894_ok
def T2891 : Node := Node.leaf L2891
theorem T2891_ok : Node.check D_R22222 T2891 [((489/128),(1141/256)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2891_ok
def T2890 : Node := Node.leaf L2890
theorem T2890_ok : Node.check D_R22222 T2890 [((2119/512),(1141/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2890_ok
def T2889 : Node := Node.leaf L2889
theorem T2889_ok : Node.check D_R22222 T2889 [((489/128),(2119/512)),((4455/2048),(1215/512)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2889_ok
def T2888 : Node := Node.leaf L2888
theorem T2888_ok : Node.check D_R22222 T2888 [((4075/1024),(2119/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2888_ok
def T2887 : Node := Node.leaf L2887
theorem T2887_ok : Node.check D_R22222 T2887 [((4075/1024),(2119/512)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2887_ok
def T2886 : Node := Node.leaf L2886
theorem T2886_ok : Node.check D_R22222 T2886 [((4075/1024),(2119/512)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2886_ok
def T2885 : Node := Node.leaf L2885
theorem T2885_ok : Node.check D_R22222 T2885 [((4075/1024),(2119/512)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2885_ok
def T2884 : Node := Node.split 2 T2885 T2886
theorem T2884_ok : Node.check D_R22222 T2884 [((4075/1024),(2119/512)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2885_ok T2886_ok
def T2883 : Node := Node.split 1 T2884 T2887
theorem T2883_ok : Node.check D_R22222 T2883 [((4075/1024),(2119/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2884_ok T2887_ok
def T2882 : Node := Node.split 3 T2883 T2888
theorem T2882_ok : Node.check D_R22222 T2882 [((4075/1024),(2119/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2883_ok T2888_ok
def T2881 : Node := Node.leaf L2881
theorem T2881_ok : Node.check D_R22222 T2881 [((489/128),(4075/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2881_ok
def T2880 : Node := Node.leaf L2880
theorem T2880_ok : Node.check D_R22222 T2880 [((489/128),(4075/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2880_ok
def T2879 : Node := Node.leaf L2879
theorem T2879_ok : Node.check D_R22222 T2879 [((489/128),(4075/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2879_ok
def T2878 : Node := Node.leaf L2878
theorem T2878_ok : Node.check D_R22222 T2878 [((489/128),(4075/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2878_ok
def T2877 : Node := Node.split 2 T2878 T2879
theorem T2877_ok : Node.check D_R22222 T2877 [((489/128),(4075/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2878_ok T2879_ok
def T2876 : Node := Node.split 1 T2877 T2880
theorem T2876_ok : Node.check D_R22222 T2876 [((489/128),(4075/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2877_ok T2880_ok
def T2875 : Node := Node.split 3 T2876 T2881
theorem T2875_ok : Node.check D_R22222 T2875 [((489/128),(4075/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2876_ok T2881_ok
def T2874 : Node := Node.split 0 T2875 T2882
theorem T2874_ok : Node.check D_R22222 T2874 [((489/128),(2119/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2875_ok T2882_ok
def T2873 : Node := Node.leaf L2873
theorem T2873_ok : Node.check D_R22222 T2873 [((489/128),(2119/512)),((2025/1024),(4455/2048)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2873_ok
def T2872 : Node := Node.split 2 T2873 T2874
theorem T2872_ok : Node.check D_R22222 T2872 [((489/128),(2119/512)),((2025/1024),(4455/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2873_ok T2874_ok
def T2871 : Node := Node.split 1 T2872 T2889
theorem T2871_ok : Node.check D_R22222 T2871 [((489/128),(2119/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2872_ok T2889_ok
def T2870 : Node := Node.leaf L2870
theorem T2870_ok : Node.check D_R22222 T2870 [((489/128),(2119/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2870_ok
def T2869 : Node := Node.split 3 T2870 T2871
theorem T2869_ok : Node.check D_R22222 T2869 [((489/128),(2119/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2870_ok T2871_ok
def T2868 : Node := Node.split 0 T2869 T2890
theorem T2868_ok : Node.check D_R22222 T2868 [((489/128),(1141/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2869_ok T2890_ok
def T2867 : Node := Node.split 2 T2868 T2891
theorem T2867_ok : Node.check D_R22222 T2867 [((489/128),(1141/256)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2868_ok T2891_ok
def T2866 : Node := Node.leaf L2866
theorem T2866_ok : Node.check D_R22222 T2866 [((489/128),(1141/256)),((405/256),(2025/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2866_ok
def T2865 : Node := Node.leaf L2865
theorem T2865_ok : Node.check D_R22222 T2865 [((489/128),(1141/256)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2865_ok
def T2864 : Node := Node.split 2 T2865 T2866
theorem T2864_ok : Node.check D_R22222 T2864 [((489/128),(1141/256)),((405/256),(2025/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2865_ok T2866_ok
def T2863 : Node := Node.split 1 T2864 T2867
theorem T2863_ok : Node.check D_R22222 T2863 [((489/128),(1141/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2864_ok T2867_ok
def T2862 : Node := Node.leaf L2862
theorem T2862_ok : Node.check D_R22222 T2862 [((489/128),(1141/256)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2862_ok
def T2861 : Node := Node.split 3 T2862 T2863
theorem T2861_ok : Node.check D_R22222 T2861 [((489/128),(1141/256)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2862_ok T2863_ok
def T2860 : Node := Node.split 0 T2861 T2892
theorem T2860_ok : Node.check D_R22222 T2860 [((489/128),(163/32)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2861_ok T2892_ok
def T2859 : Node := Node.leaf L2859
theorem T2859_ok : Node.check D_R22222 T2859 [((489/128),(163/32)),((405/256),(1215/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2859_ok
def T2858 : Node := Node.split 2 T2859 T2860
theorem T2858_ok : Node.check D_R22222 T2858 [((489/128),(163/32)),((405/256),(1215/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2859_ok T2860_ok
def T2857 : Node := Node.split 1 T2858 T2899
theorem T2857_ok : Node.check D_R22222 T2857 [((489/128),(163/32)),((405/256),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2858_ok T2899_ok
def T2856 : Node := Node.split 3 T2857 T2910
theorem T2856_ok : Node.check D_R22222 T2856 [((489/128),(163/32)),((405/256),(405/128)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2857_ok T2910_ok
def T2855 : Node := Node.leaf L2855
theorem T2855_ok : Node.check D_R22222 T2855 [((815/256),(489/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2855_ok
def T2854 : Node := Node.leaf L2854
theorem T2854_ok : Node.check D_R22222 T2854 [((163/64),(815/256)),((2835/1024),(405/128)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2854_ok
def T2853 : Node := Node.leaf L2853
theorem T2853_ok : Node.check D_R22222 T2853 [((163/64),(815/256)),((1215/512),(2835/1024)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2853_ok
def T2852 : Node := Node.split 1 T2853 T2854
theorem T2852_ok : Node.check D_R22222 T2852 [((163/64),(815/256)),((1215/512),(405/128)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2853_ok T2854_ok
def T2851 : Node := Node.leaf L2851
theorem T2851_ok : Node.check D_R22222 T2851 [((163/64),(815/256)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2851_ok
def T2850 : Node := Node.split 3 T2851 T2852
theorem T2850_ok : Node.check D_R22222 T2850 [((163/64),(815/256)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2851_ok T2852_ok
def T2849 : Node := Node.split 0 T2850 T2855
theorem T2849_ok : Node.check D_R22222 T2849 [((163/64),(489/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2850_ok T2855_ok
def T2848 : Node := Node.leaf L2848
theorem T2848_ok : Node.check D_R22222 T2848 [((163/64),(489/128)),((1215/512),(405/128)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2848_ok
def T2847 : Node := Node.split 2 T2848 T2849
theorem T2847_ok : Node.check D_R22222 T2847 [((163/64),(489/128)),((1215/512),(405/128)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2848_ok T2849_ok
def T2846 : Node := Node.leaf L2846
theorem T2846_ok : Node.check D_R22222 T2846 [((815/256),(489/128)),((2025/1024),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2846_ok
def T2845 : Node := Node.leaf L2845
theorem T2845_ok : Node.check D_R22222 T2845 [((815/256),(489/128)),((405/256),(2025/1024)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2845_ok
def T2844 : Node := Node.split 1 T2845 T2846
theorem T2844_ok : Node.check D_R22222 T2844 [((815/256),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2845_ok T2846_ok
def T2843 : Node := Node.leaf L2843
theorem T2843_ok : Node.check D_R22222 T2843 [((815/256),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2843_ok
def T2842 : Node := Node.split 3 T2843 T2844
theorem T2842_ok : Node.check D_R22222 T2842 [((815/256),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2843_ok T2844_ok
def T2841 : Node := Node.leaf L2841
theorem T2841_ok : Node.check D_R22222 T2841 [((163/64),(815/256)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2841_ok
def T2840 : Node := Node.leaf L2840
theorem T2840_ok : Node.check D_R22222 T2840 [((1467/512),(815/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L2840_ok
def T2839 : Node := Node.leaf L2839
theorem T2839_ok : Node.check D_R22222 T2839 [((1467/512),(815/256)),((4455/2048),(1215/512)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2839_ok
def T2838 : Node := Node.leaf L2838
theorem T2838_ok : Node.check D_R22222 T2838 [((3097/1024),(815/256)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2838_ok
def T2837 : Node := Node.leaf L2837
theorem T2837_ok : Node.check D_R22222 T2837 [((3097/1024),(815/256)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2837_ok
def T2836 : Node := Node.leaf L2836
theorem T2836_ok : Node.check D_R22222 T2836 [((3097/1024),(815/256)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2836_ok
def T2835 : Node := Node.leaf L2835
theorem T2835_ok : Node.check D_R22222 T2835 [((3097/1024),(815/256)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2835_ok
def T2834 : Node := Node.split 2 T2835 T2836
theorem T2834_ok : Node.check D_R22222 T2834 [((3097/1024),(815/256)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2835_ok T2836_ok
def T2833 : Node := Node.split 1 T2834 T2837
theorem T2833_ok : Node.check D_R22222 T2833 [((3097/1024),(815/256)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2834_ok T2837_ok
def T2832 : Node := Node.split 3 T2833 T2838
theorem T2832_ok : Node.check D_R22222 T2832 [((3097/1024),(815/256)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2833_ok T2838_ok
def T2831 : Node := Node.leaf L2831
theorem T2831_ok : Node.check D_R22222 T2831 [((1467/512),(3097/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2831_ok
def T2830 : Node := Node.leaf L2830
theorem T2830_ok : Node.check D_R22222 T2830 [((1467/512),(3097/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2830_ok
def T2829 : Node := Node.leaf L2829
theorem T2829_ok : Node.check D_R22222 T2829 [((1467/512),(3097/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2829_ok
def T2828 : Node := Node.leaf L2828
theorem T2828_ok : Node.check D_R22222 T2828 [((1467/512),(3097/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2828_ok
def T2827 : Node := Node.split 2 T2828 T2829
theorem T2827_ok : Node.check D_R22222 T2827 [((1467/512),(3097/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2828_ok T2829_ok
def T2826 : Node := Node.split 1 T2827 T2830
theorem T2826_ok : Node.check D_R22222 T2826 [((1467/512),(3097/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2827_ok T2830_ok
def T2825 : Node := Node.split 3 T2826 T2831
theorem T2825_ok : Node.check D_R22222 T2825 [((1467/512),(3097/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2826_ok T2831_ok
def T2824 : Node := Node.split 0 T2825 T2832
theorem T2824_ok : Node.check D_R22222 T2824 [((1467/512),(815/256)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2825_ok T2832_ok
def T2823 : Node := Node.leaf L2823
theorem T2823_ok : Node.check D_R22222 T2823 [((1467/512),(815/256)),((2025/1024),(4455/2048)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2823_ok
def T2822 : Node := Node.split 2 T2823 T2824
theorem T2822_ok : Node.check D_R22222 T2822 [((1467/512),(815/256)),((2025/1024),(4455/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2823_ok T2824_ok
def T2821 : Node := Node.split 1 T2822 T2839
theorem T2821_ok : Node.check D_R22222 T2821 [((1467/512),(815/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2822_ok T2839_ok
def T2820 : Node := Node.split 3 T2821 T2840
theorem T2820_ok : Node.check D_R22222 T2820 [((1467/512),(815/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2821_ok T2840_ok
def T2819 : Node := Node.leaf L2819
theorem T2819_ok : Node.check D_R22222 T2819 [((163/64),(1467/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2819_ok
def T2818 : Node := Node.split 0 T2819 T2820
theorem T2818_ok : Node.check D_R22222 T2818 [((163/64),(815/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2819_ok T2820_ok
def T2817 : Node := Node.split 2 T2818 T2841
theorem T2817_ok : Node.check D_R22222 T2817 [((163/64),(815/256)),((2025/1024),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2818_ok T2841_ok
def T2816 : Node := Node.leaf L2816
theorem T2816_ok : Node.check D_R22222 T2816 [((163/64),(815/256)),((405/256),(2025/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2816_ok
def T2815 : Node := Node.leaf L2815
theorem T2815_ok : Node.check D_R22222 T2815 [((163/64),(815/256)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2815_ok
def T2814 : Node := Node.split 2 T2815 T2816
theorem T2814_ok : Node.check D_R22222 T2814 [((163/64),(815/256)),((405/256),(2025/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2815_ok T2816_ok
def T2813 : Node := Node.split 1 T2814 T2817
theorem T2813_ok : Node.check D_R22222 T2813 [((163/64),(815/256)),((405/256),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2814_ok T2817_ok
def T2812 : Node := Node.leaf L2812
theorem T2812_ok : Node.check D_R22222 T2812 [((163/64),(815/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2812_ok
def T2811 : Node := Node.split 3 T2812 T2813
theorem T2811_ok : Node.check D_R22222 T2811 [((163/64),(815/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2812_ok T2813_ok
def T2810 : Node := Node.split 0 T2811 T2842
theorem T2810_ok : Node.check D_R22222 T2810 [((163/64),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2811_ok T2842_ok
def T2809 : Node := Node.leaf L2809
theorem T2809_ok : Node.check D_R22222 T2809 [((163/64),(489/128)),((405/256),(1215/512)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2809_ok
def T2808 : Node := Node.split 2 T2809 T2810
theorem T2808_ok : Node.check D_R22222 T2808 [((163/64),(489/128)),((405/256),(1215/512)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2809_ok T2810_ok
def T2807 : Node := Node.split 1 T2808 T2847
theorem T2807_ok : Node.check D_R22222 T2807 [((163/64),(489/128)),((405/256),(405/128)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2808_ok T2847_ok
def T2806 : Node := Node.leaf L2806
theorem T2806_ok : Node.check D_R22222 T2806 [((815/256),(489/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2806_ok
def T2805 : Node := Node.leaf L2805
theorem T2805_ok : Node.check D_R22222 T2805 [((815/256),(489/128)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2805_ok
def T2804 : Node := Node.split 3 T2805 T2806
theorem T2804_ok : Node.check D_R22222 T2804 [((815/256),(489/128)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2805_ok T2806_ok
def T2803 : Node := Node.leaf L2803
theorem T2803_ok : Node.check D_R22222 T2803 [((163/64),(815/256)),((2835/1024),(405/128)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2803_ok
def T2802 : Node := Node.leaf L2802
theorem T2802_ok : Node.check D_R22222 T2802 [((163/64),(815/256)),((2835/1024),(405/128)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2802_ok
def T2801 : Node := Node.split 2 T2802 T2803
theorem T2801_ok : Node.check D_R22222 T2801 [((163/64),(815/256)),((2835/1024),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2802_ok T2803_ok
def T2800 : Node := Node.leaf L2800
theorem T2800_ok : Node.check D_R22222 T2800 [((163/64),(815/256)),((1215/512),(2835/1024)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2800_ok
def T2799 : Node := Node.split 1 T2800 T2801
theorem T2799_ok : Node.check D_R22222 T2799 [((163/64),(815/256)),((1215/512),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2800_ok T2801_ok
def T2798 : Node := Node.leaf L2798
theorem T2798_ok : Node.check D_R22222 T2798 [((163/64),(815/256)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2798_ok
def T2797 : Node := Node.split 3 T2798 T2799
theorem T2797_ok : Node.check D_R22222 T2797 [((163/64),(815/256)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2798_ok T2799_ok
def T2796 : Node := Node.split 0 T2797 T2804
theorem T2796_ok : Node.check D_R22222 T2796 [((163/64),(489/128)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2797_ok T2804_ok
def T2795 : Node := Node.leaf L2795
theorem T2795_ok : Node.check D_R22222 T2795 [((163/64),(489/128)),((1215/512),(405/128)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2795_ok
def T2794 : Node := Node.split 2 T2795 T2796
theorem T2794_ok : Node.check D_R22222 T2794 [((163/64),(489/128)),((1215/512),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2795_ok T2796_ok
def T2793 : Node := Node.leaf L2793
theorem T2793_ok : Node.check D_R22222 T2793 [((815/256),(489/128)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2793_ok
def T2792 : Node := Node.leaf L2792
theorem T2792_ok : Node.check D_R22222 T2792 [((815/256),(489/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2792_ok
def T2791 : Node := Node.split 2 T2792 T2793
theorem T2791_ok : Node.check D_R22222 T2791 [((815/256),(489/128)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2792_ok T2793_ok
def T2790 : Node := Node.leaf L2790
theorem T2790_ok : Node.check D_R22222 T2790 [((815/256),(489/128)),((405/256),(2025/1024)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2790_ok
def T2789 : Node := Node.split 1 T2790 T2791
theorem T2789_ok : Node.check D_R22222 T2789 [((815/256),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2790_ok T2791_ok
def T2788 : Node := Node.leaf L2788
theorem T2788_ok : Node.check D_R22222 T2788 [((815/256),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2788_ok
def T2787 : Node := Node.split 3 T2788 T2789
theorem T2787_ok : Node.check D_R22222 T2787 [((815/256),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2788_ok T2789_ok
def T2786 : Node := Node.leaf L2786
theorem T2786_ok : Node.check D_R22222 T2786 [((163/64),(815/256)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2786_ok
def T2785 : Node := Node.leaf L2785
theorem T2785_ok : Node.check D_R22222 T2785 [((1467/512),(815/256)),((4455/2048),(1215/512)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2785_ok
def T2784 : Node := Node.leaf L2784
theorem T2784_ok : Node.check D_R22222 T2784 [((3097/1024),(815/256)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2784_ok
def T2783 : Node := Node.leaf L2783
theorem T2783_ok : Node.check D_R22222 T2783 [((3097/1024),(815/256)),((8505/4096),(4455/2048)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2783_ok
def T2782 : Node := Node.leaf L2782
theorem T2782_ok : Node.check D_R22222 T2782 [((3097/1024),(815/256)),((8505/4096),(4455/2048)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2782_ok
def T2781 : Node := Node.split 2 T2782 T2783
theorem T2781_ok : Node.check D_R22222 T2781 [((3097/1024),(815/256)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2782_ok T2783_ok
def T2780 : Node := Node.leaf L2780
theorem T2780_ok : Node.check D_R22222 T2780 [((3097/1024),(815/256)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2780_ok
def T2779 : Node := Node.leaf L2779
theorem T2779_ok : Node.check D_R22222 T2779 [((3097/1024),(815/256)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2779_ok
def T2778 : Node := Node.split 2 T2779 T2780
theorem T2778_ok : Node.check D_R22222 T2778 [((3097/1024),(815/256)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2779_ok T2780_ok
def T2777 : Node := Node.split 1 T2778 T2781
theorem T2777_ok : Node.check D_R22222 T2777 [((3097/1024),(815/256)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2778_ok T2781_ok
def T2776 : Node := Node.split 3 T2777 T2784
theorem T2776_ok : Node.check D_R22222 T2776 [((3097/1024),(815/256)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2777_ok T2784_ok
def T2775 : Node := Node.leaf L2775
theorem T2775_ok : Node.check D_R22222 T2775 [((1467/512),(3097/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2775_ok
def T2774 : Node := Node.leaf L2774
theorem T2774_ok : Node.check D_R22222 T2774 [((1467/512),(3097/1024)),((8505/4096),(4455/2048)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2774_ok
def T2773 : Node := Node.leaf L2773
theorem T2773_ok : Node.check D_R22222 T2773 [((1467/512),(3097/1024)),((8505/4096),(4455/2048)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2773_ok
def T2772 : Node := Node.split 2 T2773 T2774
theorem T2772_ok : Node.check D_R22222 T2772 [((1467/512),(3097/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2773_ok T2774_ok
def T2771 : Node := Node.leaf L2771
theorem T2771_ok : Node.check D_R22222 T2771 [((1467/512),(3097/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2771_ok
def T2770 : Node := Node.leaf L2770
theorem T2770_ok : Node.check D_R22222 T2770 [((1467/512),(3097/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2770_ok
def T2769 : Node := Node.split 2 T2770 T2771
theorem T2769_ok : Node.check D_R22222 T2769 [((1467/512),(3097/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2770_ok T2771_ok
def T2768 : Node := Node.split 1 T2769 T2772
theorem T2768_ok : Node.check D_R22222 T2768 [((1467/512),(3097/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2769_ok T2772_ok
def T2767 : Node := Node.split 3 T2768 T2775
theorem T2767_ok : Node.check D_R22222 T2767 [((1467/512),(3097/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2768_ok T2775_ok
def T2766 : Node := Node.split 0 T2767 T2776
theorem T2766_ok : Node.check D_R22222 T2766 [((1467/512),(815/256)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2767_ok T2776_ok
def T2765 : Node := Node.leaf L2765
theorem T2765_ok : Node.check D_R22222 T2765 [((1467/512),(815/256)),((2025/1024),(4455/2048)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2765_ok
def T2764 : Node := Node.split 2 T2765 T2766
theorem T2764_ok : Node.check D_R22222 T2764 [((1467/512),(815/256)),((2025/1024),(4455/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2765_ok T2766_ok
def T2763 : Node := Node.split 1 T2764 T2785
theorem T2763_ok : Node.check D_R22222 T2763 [((1467/512),(815/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2764_ok T2785_ok
def T2762 : Node := Node.leaf L2762
theorem T2762_ok : Node.check D_R22222 T2762 [((1467/512),(815/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2762_ok
def T2761 : Node := Node.split 3 T2762 T2763
theorem T2761_ok : Node.check D_R22222 T2761 [((1467/512),(815/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2762_ok T2763_ok
def T2760 : Node := Node.leaf L2760
theorem T2760_ok : Node.check D_R22222 T2760 [((163/64),(1467/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2760_ok
def T2759 : Node := Node.split 0 T2760 T2761
theorem T2759_ok : Node.check D_R22222 T2759 [((163/64),(815/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2760_ok T2761_ok
def T2758 : Node := Node.split 2 T2759 T2786
theorem T2758_ok : Node.check D_R22222 T2758 [((163/64),(815/256)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2759_ok T2786_ok
def T2757 : Node := Node.leaf L2757
theorem T2757_ok : Node.check D_R22222 T2757 [((163/64),(815/256)),((405/256),(2025/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2757_ok
def T2756 : Node := Node.leaf L2756
theorem T2756_ok : Node.check D_R22222 T2756 [((3097/1024),(815/256)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2756_ok
def T2755 : Node := Node.leaf L2755
theorem T2755_ok : Node.check D_R22222 T2755 [((3097/1024),(815/256)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2755_ok
def T2754 : Node := Node.leaf L2754
theorem T2754_ok : Node.check D_R22222 T2754 [((3097/1024),(815/256)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2754_ok
def T2753 : Node := Node.split 2 T2754 T2755
theorem T2753_ok : Node.check D_R22222 T2753 [((3097/1024),(815/256)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2754_ok T2755_ok
def T2752 : Node := Node.leaf L2752
theorem T2752_ok : Node.check D_R22222 T2752 [((3097/1024),(815/256)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2752_ok
def T2751 : Node := Node.split 1 T2752 T2753
theorem T2751_ok : Node.check D_R22222 T2751 [((3097/1024),(815/256)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2752_ok T2753_ok
def T2750 : Node := Node.split 3 T2751 T2756
theorem T2750_ok : Node.check D_R22222 T2750 [((3097/1024),(815/256)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2751_ok T2756_ok
def T2749 : Node := Node.leaf L2749
theorem T2749_ok : Node.check D_R22222 T2749 [((1467/512),(3097/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2749_ok
def T2748 : Node := Node.leaf L2748
theorem T2748_ok : Node.check D_R22222 T2748 [((1467/512),(3097/1024)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2748_ok
def T2747 : Node := Node.leaf L2747
theorem T2747_ok : Node.check D_R22222 T2747 [((1467/512),(3097/1024)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2747_ok
def T2746 : Node := Node.split 2 T2747 T2748
theorem T2746_ok : Node.check D_R22222 T2746 [((1467/512),(3097/1024)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2747_ok T2748_ok
def T2745 : Node := Node.leaf L2745
theorem T2745_ok : Node.check D_R22222 T2745 [((1467/512),(3097/1024)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2745_ok
def T2744 : Node := Node.split 1 T2745 T2746
theorem T2744_ok : Node.check D_R22222 T2744 [((1467/512),(3097/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2745_ok T2746_ok
def T2743 : Node := Node.split 3 T2744 T2749
theorem T2743_ok : Node.check D_R22222 T2743 [((1467/512),(3097/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2744_ok T2749_ok
def T2742 : Node := Node.split 0 T2743 T2750
theorem T2742_ok : Node.check D_R22222 T2742 [((1467/512),(815/256)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2743_ok T2750_ok
def T2741 : Node := Node.leaf L2741
theorem T2741_ok : Node.check D_R22222 T2741 [((1467/512),(815/256)),((3645/2048),(2025/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2741_ok
def T2740 : Node := Node.split 2 T2741 T2742
theorem T2740_ok : Node.check D_R22222 T2740 [((1467/512),(815/256)),((3645/2048),(2025/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2741_ok T2742_ok
def T2739 : Node := Node.leaf L2739
theorem T2739_ok : Node.check D_R22222 T2739 [((1467/512),(815/256)),((405/256),(3645/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2739_ok
def T2738 : Node := Node.split 1 T2739 T2740
theorem T2738_ok : Node.check D_R22222 T2738 [((1467/512),(815/256)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2739_ok T2740_ok
def T2737 : Node := Node.leaf L2737
theorem T2737_ok : Node.check D_R22222 T2737 [((1467/512),(815/256)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2737_ok
def T2736 : Node := Node.split 3 T2737 T2738
theorem T2736_ok : Node.check D_R22222 T2736 [((1467/512),(815/256)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2737_ok T2738_ok
def T2735 : Node := Node.leaf L2735
theorem T2735_ok : Node.check D_R22222 T2735 [((163/64),(1467/512)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2735_ok
def T2734 : Node := Node.split 0 T2735 T2736
theorem T2734_ok : Node.check D_R22222 T2734 [((163/64),(815/256)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2735_ok T2736_ok
def T2733 : Node := Node.split 2 T2734 T2757
theorem T2733_ok : Node.check D_R22222 T2733 [((163/64),(815/256)),((405/256),(2025/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2734_ok T2757_ok
def T2732 : Node := Node.split 1 T2733 T2758
theorem T2732_ok : Node.check D_R22222 T2732 [((163/64),(815/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2733_ok T2758_ok
def T2731 : Node := Node.leaf L2731
theorem T2731_ok : Node.check D_R22222 T2731 [((163/64),(815/256)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2731_ok
def T2730 : Node := Node.split 3 T2731 T2732
theorem T2730_ok : Node.check D_R22222 T2730 [((163/64),(815/256)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2731_ok T2732_ok
def T2729 : Node := Node.split 0 T2730 T2787
theorem T2729_ok : Node.check D_R22222 T2729 [((163/64),(489/128)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2730_ok T2787_ok
def T2728 : Node := Node.leaf L2728
theorem T2728_ok : Node.check D_R22222 T2728 [((163/64),(489/128)),((405/256),(1215/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2728_ok
def T2727 : Node := Node.split 2 T2728 T2729
theorem T2727_ok : Node.check D_R22222 T2727 [((163/64),(489/128)),((405/256),(1215/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2728_ok T2729_ok
def T2726 : Node := Node.split 1 T2727 T2794
theorem T2726_ok : Node.check D_R22222 T2726 [((163/64),(489/128)),((405/256),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2727_ok T2794_ok
def T2725 : Node := Node.split 3 T2726 T2807
theorem T2725_ok : Node.check D_R22222 T2725 [((163/64),(489/128)),((405/256),(405/128)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2726_ok T2807_ok
def T2724 : Node := Node.split 0 T2725 T2856
theorem T2724_ok : Node.check D_R22222 T2724 [((163/64),(163/32)),((405/256),(405/128)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2725_ok T2856_ok
def T2723 : Node := Node.split 2 T2724 T2925
theorem T2723_ok : Node.check D_R22222 T2723 [((163/64),(163/32)),((405/256),(405/128)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2724_ok T2925_ok
def T2722 : Node := Node.leaf L2722
theorem T2722_ok : Node.check D_R22222 T2722 [((489/128),(163/32)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2722_ok
def T2721 : Node := Node.leaf L2721
theorem T2721_ok : Node.check D_R22222 T2721 [((1141/256),(163/32)),((405/512),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2721_ok
def T2720 : Node := Node.leaf L2720
theorem T2720_ok : Node.check D_R22222 T2720 [((1141/256),(163/32)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2720_ok
def T2719 : Node := Node.split 3 T2720 T2721
theorem T2719_ok : Node.check D_R22222 T2719 [((1141/256),(163/32)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2720_ok T2721_ok
def T2718 : Node := Node.leaf L2718
theorem T2718_ok : Node.check D_R22222 T2718 [((489/128),(1141/256)),((1215/1024),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2718_ok
def T2717 : Node := Node.leaf L2717
theorem T2717_ok : Node.check D_R22222 T2717 [((489/128),(1141/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2717_ok
def T2716 : Node := Node.leaf L2716
theorem T2716_ok : Node.check D_R22222 T2716 [((489/128),(1141/256)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2716_ok
def T2715 : Node := Node.split 2 T2716 T2717
theorem T2715_ok : Node.check D_R22222 T2715 [((489/128),(1141/256)),((405/512),(1215/1024)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2716_ok T2717_ok
def T2714 : Node := Node.split 1 T2715 T2718
theorem T2714_ok : Node.check D_R22222 T2714 [((489/128),(1141/256)),((405/512),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2715_ok T2718_ok
def T2713 : Node := Node.leaf L2713
theorem T2713_ok : Node.check D_R22222 T2713 [((489/128),(1141/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2713_ok
def T2712 : Node := Node.split 3 T2713 T2714
theorem T2712_ok : Node.check D_R22222 T2712 [((489/128),(1141/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2713_ok T2714_ok
def T2711 : Node := Node.split 0 T2712 T2719
theorem T2711_ok : Node.check D_R22222 T2711 [((489/128),(163/32)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2712_ok T2719_ok
def T2710 : Node := Node.split 2 T2711 T2722
theorem T2710_ok : Node.check D_R22222 T2710 [((489/128),(163/32)),((405/512),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2711_ok T2722_ok
def T2709 : Node := Node.leaf L2709
theorem T2709_ok : Node.check D_R22222 T2709 [((489/128),(163/32)),((0),(405/512)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2709_ok
def T2708 : Node := Node.split 1 T2709 T2710
theorem T2708_ok : Node.check D_R22222 T2708 [((489/128),(163/32)),((0),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2709_ok T2710_ok
def T2707 : Node := Node.leaf L2707
theorem T2707_ok : Node.check D_R22222 T2707 [((1141/256),(163/32)),((405/512),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2707_ok
def T2706 : Node := Node.leaf L2706
theorem T2706_ok : Node.check D_R22222 T2706 [((1141/256),(163/32)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2706_ok
def T2705 : Node := Node.split 3 T2706 T2707
theorem T2705_ok : Node.check D_R22222 T2705 [((1141/256),(163/32)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2706_ok T2707_ok
def T2704 : Node := Node.leaf L2704
theorem T2704_ok : Node.check D_R22222 T2704 [((489/128),(1141/256)),((1215/1024),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2704_ok
def T2703 : Node := Node.leaf L2703
theorem T2703_ok : Node.check D_R22222 T2703 [((489/128),(1141/256)),((405/512),(1215/1024)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2703_ok
def T2702 : Node := Node.split 1 T2703 T2704
theorem T2702_ok : Node.check D_R22222 T2702 [((489/128),(1141/256)),((405/512),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2703_ok T2704_ok
def T2701 : Node := Node.leaf L2701
theorem T2701_ok : Node.check D_R22222 T2701 [((489/128),(1141/256)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2701_ok
def T2700 : Node := Node.split 3 T2701 T2702
theorem T2700_ok : Node.check D_R22222 T2700 [((489/128),(1141/256)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2701_ok T2702_ok
def T2699 : Node := Node.split 0 T2700 T2705
theorem T2699_ok : Node.check D_R22222 T2699 [((489/128),(163/32)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2700_ok T2705_ok
def T2698 : Node := Node.leaf L2698
theorem T2698_ok : Node.check D_R22222 T2698 [((1141/256),(163/32)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2698_ok
def T2697 : Node := Node.leaf L2697
theorem T2697_ok : Node.check D_R22222 T2697 [((1141/256),(163/32)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2697_ok
def T2696 : Node := Node.leaf L2696
theorem T2696_ok : Node.check D_R22222 T2696 [((1141/256),(163/32)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2696_ok
def T2695 : Node := Node.split 2 T2696 T2697
theorem T2695_ok : Node.check D_R22222 T2695 [((1141/256),(163/32)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2696_ok T2697_ok
def T2694 : Node := Node.split 1 T2695 T2698
theorem T2694_ok : Node.check D_R22222 T2694 [((1141/256),(163/32)),((405/512),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2695_ok T2698_ok
def T2693 : Node := Node.leaf L2693
theorem T2693_ok : Node.check D_R22222 T2693 [((1141/256),(163/32)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2693_ok
def T2692 : Node := Node.split 3 T2693 T2694
theorem T2692_ok : Node.check D_R22222 T2692 [((1141/256),(163/32)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2693_ok T2694_ok
def T2691 : Node := Node.leaf L2691
theorem T2691_ok : Node.check D_R22222 T2691 [((489/128),(1141/256)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2691_ok
def T2690 : Node := Node.leaf L2690
theorem T2690_ok : Node.check D_R22222 T2690 [((2119/512),(1141/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2690_ok
def T2689 : Node := Node.leaf L2689
theorem T2689_ok : Node.check D_R22222 T2689 [((489/128),(2119/512)),((2025/2048),(1215/1024)),((4455/2048),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2689_ok
def T2688 : Node := Node.leaf L2688
theorem T2688_ok : Node.check D_R22222 T2688 [((4075/1024),(2119/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2688_ok
def T2687 : Node := Node.leaf L2687
theorem T2687_ok : Node.check D_R22222 T2687 [((4075/1024),(2119/512)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2687_ok
def T2686 : Node := Node.leaf L2686
theorem T2686_ok : Node.check D_R22222 T2686 [((4075/1024),(2119/512)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2686_ok
def T2685 : Node := Node.leaf L2685
theorem T2685_ok : Node.check D_R22222 T2685 [((4075/1024),(2119/512)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2685_ok
def T2684 : Node := Node.split 2 T2685 T2686
theorem T2684_ok : Node.check D_R22222 T2684 [((4075/1024),(2119/512)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2685_ok T2686_ok
def T2683 : Node := Node.split 1 T2684 T2687
theorem T2683_ok : Node.check D_R22222 T2683 [((4075/1024),(2119/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2684_ok T2687_ok
def T2682 : Node := Node.split 3 T2683 T2688
theorem T2682_ok : Node.check D_R22222 T2682 [((4075/1024),(2119/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2683_ok T2688_ok
def T2681 : Node := Node.leaf L2681
theorem T2681_ok : Node.check D_R22222 T2681 [((489/128),(4075/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2681_ok
def T2680 : Node := Node.leaf L2680
theorem T2680_ok : Node.check D_R22222 T2680 [((489/128),(4075/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2680_ok
def T2679 : Node := Node.leaf L2679
theorem T2679_ok : Node.check D_R22222 T2679 [((489/128),(4075/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2679_ok
def T2678 : Node := Node.leaf L2678
theorem T2678_ok : Node.check D_R22222 T2678 [((489/128),(4075/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2678_ok
def T2677 : Node := Node.split 2 T2678 T2679
theorem T2677_ok : Node.check D_R22222 T2677 [((489/128),(4075/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2678_ok T2679_ok
def T2676 : Node := Node.split 1 T2677 T2680
theorem T2676_ok : Node.check D_R22222 T2676 [((489/128),(4075/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2677_ok T2680_ok
def T2675 : Node := Node.split 3 T2676 T2681
theorem T2675_ok : Node.check D_R22222 T2675 [((489/128),(4075/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2676_ok T2681_ok
def T2674 : Node := Node.split 0 T2675 T2682
theorem T2674_ok : Node.check D_R22222 T2674 [((489/128),(2119/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2675_ok T2682_ok
def T2673 : Node := Node.split 2 T2674 T2689
theorem T2673_ok : Node.check D_R22222 T2673 [((489/128),(2119/512)),((2025/2048),(1215/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2674_ok T2689_ok
def T2672 : Node := Node.leaf L2672
theorem T2672_ok : Node.check D_R22222 T2672 [((489/128),(2119/512)),((405/512),(2025/2048)),((2025/1024),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2672_ok
def T2671 : Node := Node.split 1 T2672 T2673
theorem T2671_ok : Node.check D_R22222 T2671 [((489/128),(2119/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2672_ok T2673_ok
def T2670 : Node := Node.leaf L2670
theorem T2670_ok : Node.check D_R22222 T2670 [((489/128),(2119/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2670_ok
def T2669 : Node := Node.split 3 T2670 T2671
theorem T2669_ok : Node.check D_R22222 T2669 [((489/128),(2119/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2670_ok T2671_ok
def T2668 : Node := Node.split 0 T2669 T2690
theorem T2668_ok : Node.check D_R22222 T2668 [((489/128),(1141/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2669_ok T2690_ok
def T2667 : Node := Node.leaf L2667
theorem T2667_ok : Node.check D_R22222 T2667 [((489/128),(1141/256)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2667_ok
def T2666 : Node := Node.split 2 T2667 T2668
theorem T2666_ok : Node.check D_R22222 T2666 [((489/128),(1141/256)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2667_ok T2668_ok
def T2665 : Node := Node.split 1 T2666 T2691
theorem T2665_ok : Node.check D_R22222 T2665 [((489/128),(1141/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2666_ok T2691_ok
def T2664 : Node := Node.leaf L2664
theorem T2664_ok : Node.check D_R22222 T2664 [((489/128),(1141/256)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2664_ok
def T2663 : Node := Node.split 3 T2664 T2665
theorem T2663_ok : Node.check D_R22222 T2663 [((489/128),(1141/256)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2664_ok T2665_ok
def T2662 : Node := Node.split 0 T2663 T2692
theorem T2662_ok : Node.check D_R22222 T2662 [((489/128),(163/32)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2663_ok T2692_ok
def T2661 : Node := Node.split 2 T2662 T2699
theorem T2661_ok : Node.check D_R22222 T2661 [((489/128),(163/32)),((405/512),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2662_ok T2699_ok
def T2660 : Node := Node.leaf L2660
theorem T2660_ok : Node.check D_R22222 T2660 [((489/128),(163/32)),((0),(405/512)),((405/256),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2660_ok
def T2659 : Node := Node.split 1 T2660 T2661
theorem T2659_ok : Node.check D_R22222 T2659 [((489/128),(163/32)),((0),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2660_ok T2661_ok
def T2658 : Node := Node.split 3 T2659 T2708
theorem T2658_ok : Node.check D_R22222 T2658 [((489/128),(163/32)),((0),(405/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2659_ok T2708_ok
def T2657 : Node := Node.leaf L2657
theorem T2657_ok : Node.check D_R22222 T2657 [((815/256),(489/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2657_ok
def T2656 : Node := Node.leaf L2656
theorem T2656_ok : Node.check D_R22222 T2656 [((163/64),(815/256)),((1215/1024),(405/256)),((1215/512),(405/128)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2656_ok
def T2655 : Node := Node.leaf L2655
theorem T2655_ok : Node.check D_R22222 T2655 [((163/64),(815/256)),((405/512),(1215/1024)),((2835/1024),(405/128)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2655_ok
def T2654 : Node := Node.leaf L2654
theorem T2654_ok : Node.check D_R22222 T2654 [((163/64),(815/256)),((405/512),(1215/1024)),((1215/512),(2835/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2654_ok
def T2653 : Node := Node.split 2 T2654 T2655
theorem T2653_ok : Node.check D_R22222 T2653 [((163/64),(815/256)),((405/512),(1215/1024)),((1215/512),(405/128)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2654_ok T2655_ok
def T2652 : Node := Node.split 1 T2653 T2656
theorem T2652_ok : Node.check D_R22222 T2652 [((163/64),(815/256)),((405/512),(405/256)),((1215/512),(405/128)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2653_ok T2656_ok
def T2651 : Node := Node.leaf L2651
theorem T2651_ok : Node.check D_R22222 T2651 [((163/64),(815/256)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2651_ok
def T2650 : Node := Node.split 3 T2651 T2652
theorem T2650_ok : Node.check D_R22222 T2650 [((163/64),(815/256)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2651_ok T2652_ok
def T2649 : Node := Node.split 0 T2650 T2657
theorem T2649_ok : Node.check D_R22222 T2649 [((163/64),(489/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2650_ok T2657_ok
def T2648 : Node := Node.leaf L2648
theorem T2648_ok : Node.check D_R22222 T2648 [((815/256),(489/128)),((1215/1024),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2648_ok
def T2647 : Node := Node.leaf L2647
theorem T2647_ok : Node.check D_R22222 T2647 [((815/256),(489/128)),((405/512),(1215/1024)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2647_ok
def T2646 : Node := Node.split 1 T2647 T2648
theorem T2646_ok : Node.check D_R22222 T2646 [((815/256),(489/128)),((405/512),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2647_ok T2648_ok
def T2645 : Node := Node.leaf L2645
theorem T2645_ok : Node.check D_R22222 T2645 [((815/256),(489/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2645_ok
def T2644 : Node := Node.split 3 T2645 T2646
theorem T2644_ok : Node.check D_R22222 T2644 [((815/256),(489/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2645_ok T2646_ok
def T2643 : Node := Node.leaf L2643
theorem T2643_ok : Node.check D_R22222 T2643 [((163/64),(815/256)),((1215/1024),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2643_ok
def T2642 : Node := Node.leaf L2642
theorem T2642_ok : Node.check D_R22222 T2642 [((1467/512),(815/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L2642_ok
def T2641 : Node := Node.leaf L2641
theorem T2641_ok : Node.check D_R22222 T2641 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((4455/2048),(1215/512)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2641_ok
def T2640 : Node := Node.leaf L2640
theorem T2640_ok : Node.check D_R22222 T2640 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2640_ok
def T2639 : Node := Node.leaf L2639
theorem T2639_ok : Node.check D_R22222 T2639 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2639_ok
def T2638 : Node := Node.leaf L2638
theorem T2638_ok : Node.check D_R22222 T2638 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2638_ok
def T2637 : Node := Node.leaf L2637
theorem T2637_ok : Node.check D_R22222 T2637 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2637_ok
def T2636 : Node := Node.split 2 T2637 T2638
theorem T2636_ok : Node.check D_R22222 T2636 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2637_ok T2638_ok
def T2635 : Node := Node.split 1 T2636 T2639
theorem T2635_ok : Node.check D_R22222 T2635 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2636_ok T2639_ok
def T2634 : Node := Node.split 3 T2635 T2640
theorem T2634_ok : Node.check D_R22222 T2634 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2635_ok T2640_ok
def T2633 : Node := Node.leaf L2633
theorem T2633_ok : Node.check D_R22222 T2633 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2633_ok
def T2632 : Node := Node.leaf L2632
theorem T2632_ok : Node.check D_R22222 T2632 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2632_ok
def T2631 : Node := Node.leaf L2631
theorem T2631_ok : Node.check D_R22222 T2631 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2631_ok
def T2630 : Node := Node.leaf L2630
theorem T2630_ok : Node.check D_R22222 T2630 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2630_ok
def T2629 : Node := Node.split 2 T2630 T2631
theorem T2629_ok : Node.check D_R22222 T2629 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2630_ok T2631_ok
def T2628 : Node := Node.split 1 T2629 T2632
theorem T2628_ok : Node.check D_R22222 T2628 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2629_ok T2632_ok
def T2627 : Node := Node.split 3 T2628 T2633
theorem T2627_ok : Node.check D_R22222 T2627 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2628_ok T2633_ok
def T2626 : Node := Node.split 0 T2627 T2634
theorem T2626_ok : Node.check D_R22222 T2626 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2627_ok T2634_ok
def T2625 : Node := Node.split 2 T2626 T2641
theorem T2625_ok : Node.check D_R22222 T2625 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2626_ok T2641_ok
def T2624 : Node := Node.leaf L2624
theorem T2624_ok : Node.check D_R22222 T2624 [((1467/512),(815/256)),((405/512),(2025/2048)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2624_ok
def T2623 : Node := Node.split 1 T2624 T2625
theorem T2623_ok : Node.check D_R22222 T2623 [((1467/512),(815/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2624_ok T2625_ok
def T2622 : Node := Node.split 3 T2623 T2642
theorem T2622_ok : Node.check D_R22222 T2622 [((1467/512),(815/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2623_ok T2642_ok
def T2621 : Node := Node.leaf L2621
theorem T2621_ok : Node.check D_R22222 T2621 [((163/64),(1467/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2621_ok
def T2620 : Node := Node.split 0 T2621 T2622
theorem T2620_ok : Node.check D_R22222 T2620 [((163/64),(815/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2621_ok T2622_ok
def T2619 : Node := Node.leaf L2619
theorem T2619_ok : Node.check D_R22222 T2619 [((163/64),(815/256)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2619_ok
def T2618 : Node := Node.split 2 T2619 T2620
theorem T2618_ok : Node.check D_R22222 T2618 [((163/64),(815/256)),((405/512),(1215/1024)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2619_ok T2620_ok
def T2617 : Node := Node.split 1 T2618 T2643
theorem T2617_ok : Node.check D_R22222 T2617 [((163/64),(815/256)),((405/512),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2618_ok T2643_ok
def T2616 : Node := Node.leaf L2616
theorem T2616_ok : Node.check D_R22222 T2616 [((163/64),(815/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2616_ok
def T2615 : Node := Node.split 3 T2616 T2617
theorem T2615_ok : Node.check D_R22222 T2615 [((163/64),(815/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2616_ok T2617_ok
def T2614 : Node := Node.split 0 T2615 T2644
theorem T2614_ok : Node.check D_R22222 T2614 [((163/64),(489/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2615_ok T2644_ok
def T2613 : Node := Node.split 2 T2614 T2649
theorem T2613_ok : Node.check D_R22222 T2613 [((163/64),(489/128)),((405/512),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2614_ok T2649_ok
def T2612 : Node := Node.leaf L2612
theorem T2612_ok : Node.check D_R22222 T2612 [((163/64),(489/128)),((0),(405/512)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2612_ok
def T2611 : Node := Node.split 1 T2612 T2613
theorem T2611_ok : Node.check D_R22222 T2611 [((163/64),(489/128)),((0),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2612_ok T2613_ok
def T2610 : Node := Node.leaf L2610
theorem T2610_ok : Node.check D_R22222 T2610 [((815/256),(489/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2610_ok
def T2609 : Node := Node.leaf L2609
theorem T2609_ok : Node.check D_R22222 T2609 [((815/256),(489/128)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2609_ok
def T2608 : Node := Node.split 3 T2609 T2610
theorem T2608_ok : Node.check D_R22222 T2608 [((815/256),(489/128)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2609_ok T2610_ok
def T2607 : Node := Node.leaf L2607
theorem T2607_ok : Node.check D_R22222 T2607 [((163/64),(815/256)),((1215/1024),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2607_ok
def T2606 : Node := Node.leaf L2606
theorem T2606_ok : Node.check D_R22222 T2606 [((163/64),(815/256)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2606_ok
def T2605 : Node := Node.leaf L2605
theorem T2605_ok : Node.check D_R22222 T2605 [((163/64),(815/256)),((405/512),(1215/1024)),((1215/512),(2835/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2605_ok
def T2604 : Node := Node.split 2 T2605 T2606
theorem T2604_ok : Node.check D_R22222 T2604 [((163/64),(815/256)),((405/512),(1215/1024)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2605_ok T2606_ok
def T2603 : Node := Node.split 1 T2604 T2607
theorem T2603_ok : Node.check D_R22222 T2603 [((163/64),(815/256)),((405/512),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2604_ok T2607_ok
def T2602 : Node := Node.leaf L2602
theorem T2602_ok : Node.check D_R22222 T2602 [((163/64),(815/256)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2602_ok
def T2601 : Node := Node.split 3 T2602 T2603
theorem T2601_ok : Node.check D_R22222 T2601 [((163/64),(815/256)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2602_ok T2603_ok
def T2600 : Node := Node.split 0 T2601 T2608
theorem T2600_ok : Node.check D_R22222 T2600 [((163/64),(489/128)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2601_ok T2608_ok
def T2599 : Node := Node.leaf L2599
theorem T2599_ok : Node.check D_R22222 T2599 [((815/256),(489/128)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2599_ok
def T2598 : Node := Node.leaf L2598
theorem T2598_ok : Node.check D_R22222 T2598 [((815/256),(489/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2598_ok
def T2597 : Node := Node.leaf L2597
theorem T2597_ok : Node.check D_R22222 T2597 [((815/256),(489/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2597_ok
def T2596 : Node := Node.split 2 T2597 T2598
theorem T2596_ok : Node.check D_R22222 T2596 [((815/256),(489/128)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2597_ok T2598_ok
def T2595 : Node := Node.split 1 T2596 T2599
theorem T2595_ok : Node.check D_R22222 T2595 [((815/256),(489/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2596_ok T2599_ok
def T2594 : Node := Node.leaf L2594
theorem T2594_ok : Node.check D_R22222 T2594 [((815/256),(489/128)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2594_ok
def T2593 : Node := Node.split 3 T2594 T2595
theorem T2593_ok : Node.check D_R22222 T2593 [((815/256),(489/128)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2594_ok T2595_ok
def T2592 : Node := Node.leaf L2592
theorem T2592_ok : Node.check D_R22222 T2592 [((163/64),(815/256)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2592_ok
def T2591 : Node := Node.leaf L2591
theorem T2591_ok : Node.check D_R22222 T2591 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((4455/2048),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2591_ok
def T2590 : Node := Node.leaf L2590
theorem T2590_ok : Node.check D_R22222 T2590 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2590_ok
def T2589 : Node := Node.leaf L2589
theorem T2589_ok : Node.check D_R22222 T2589 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2589_ok
def T2588 : Node := Node.leaf L2588
theorem T2588_ok : Node.check D_R22222 T2588 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2588_ok
def T2587 : Node := Node.split 2 T2588 T2589
theorem T2587_ok : Node.check D_R22222 T2587 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2588_ok T2589_ok
def T2586 : Node := Node.leaf L2586
theorem T2586_ok : Node.check D_R22222 T2586 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2586_ok
def T2585 : Node := Node.leaf L2585
theorem T2585_ok : Node.check D_R22222 T2585 [((6357/2048),(815/256)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2585_ok
def T2584 : Node := Node.leaf L2584
theorem T2584_ok : Node.check D_R22222 T2584 [((3097/1024),(6357/2048)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2584_ok
def T2583 : Node := Node.split 0 T2584 T2585
theorem T2583_ok : Node.check D_R22222 T2583 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2584_ok T2585_ok
def T2582 : Node := Node.split 2 T2583 T2586
theorem T2582_ok : Node.check D_R22222 T2582 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2583_ok T2586_ok
def T2581 : Node := Node.split 1 T2582 T2587
theorem T2581_ok : Node.check D_R22222 T2581 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2582_ok T2587_ok
def T2580 : Node := Node.split 3 T2581 T2590
theorem T2580_ok : Node.check D_R22222 T2580 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2581_ok T2590_ok
def T2579 : Node := Node.leaf L2579
theorem T2579_ok : Node.check D_R22222 T2579 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2579_ok
def T2578 : Node := Node.leaf L2578
theorem T2578_ok : Node.check D_R22222 T2578 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2578_ok
def T2577 : Node := Node.leaf L2577
theorem T2577_ok : Node.check D_R22222 T2577 [((6031/2048),(3097/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2577_ok
def T2576 : Node := Node.leaf L2576
theorem T2576_ok : Node.check D_R22222 T2576 [((6031/2048),(3097/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L2576_ok
def T2575 : Node := Node.split 3 T2576 T2577
theorem T2575_ok : Node.check D_R22222 T2575 [((6031/2048),(3097/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2576_ok T2577_ok
def T2574 : Node := Node.leaf L2574
theorem T2574_ok : Node.check D_R22222 T2574 [((1467/512),(6031/2048)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2574_ok
def T2573 : Node := Node.split 0 T2574 T2575
theorem T2573_ok : Node.check D_R22222 T2573 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2574_ok T2575_ok
def T2572 : Node := Node.split 2 T2573 T2578
theorem T2572_ok : Node.check D_R22222 T2572 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2573_ok T2578_ok
def T2571 : Node := Node.leaf L2571
theorem T2571_ok : Node.check D_R22222 T2571 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2571_ok
def T2570 : Node := Node.leaf L2570
theorem T2570_ok : Node.check D_R22222 T2570 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2570_ok
def T2569 : Node := Node.split 2 T2570 T2571
theorem T2569_ok : Node.check D_R22222 T2569 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2570_ok T2571_ok
def T2568 : Node := Node.split 1 T2569 T2572
theorem T2568_ok : Node.check D_R22222 T2568 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2569_ok T2572_ok
def T2567 : Node := Node.split 3 T2568 T2579
theorem T2567_ok : Node.check D_R22222 T2567 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2568_ok T2579_ok
def T2566 : Node := Node.split 0 T2567 T2580
theorem T2566_ok : Node.check D_R22222 T2566 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2567_ok T2580_ok
def T2565 : Node := Node.split 2 T2566 T2591
theorem T2565_ok : Node.check D_R22222 T2565 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2566_ok T2591_ok
def T2564 : Node := Node.leaf L2564
theorem T2564_ok : Node.check D_R22222 T2564 [((1467/512),(815/256)),((405/512),(2025/2048)),((2025/1024),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2564_ok
def T2563 : Node := Node.split 1 T2564 T2565
theorem T2563_ok : Node.check D_R22222 T2563 [((1467/512),(815/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2564_ok T2565_ok
def T2562 : Node := Node.leaf L2562
theorem T2562_ok : Node.check D_R22222 T2562 [((1467/512),(815/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2562_ok
def T2561 : Node := Node.split 3 T2562 T2563
theorem T2561_ok : Node.check D_R22222 T2561 [((1467/512),(815/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2562_ok T2563_ok
def T2560 : Node := Node.leaf L2560
theorem T2560_ok : Node.check D_R22222 T2560 [((163/64),(1467/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2560_ok
def T2559 : Node := Node.split 0 T2560 T2561
theorem T2559_ok : Node.check D_R22222 T2559 [((163/64),(815/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2560_ok T2561_ok
def T2558 : Node := Node.leaf L2558
theorem T2558_ok : Node.check D_R22222 T2558 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2558_ok
def T2557 : Node := Node.leaf L2557
theorem T2557_ok : Node.check D_R22222 T2557 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2557_ok
def T2556 : Node := Node.leaf L2556
theorem T2556_ok : Node.check D_R22222 T2556 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2556_ok
def T2555 : Node := Node.leaf L2555
theorem T2555_ok : Node.check D_R22222 T2555 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((3645/2048),(7695/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2555_ok
def T2554 : Node := Node.split 2 T2555 T2556
theorem T2554_ok : Node.check D_R22222 T2554 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2555_ok T2556_ok
def T2553 : Node := Node.split 1 T2554 T2557
theorem T2553_ok : Node.check D_R22222 T2553 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2554_ok T2557_ok
def T2552 : Node := Node.split 3 T2553 T2558
theorem T2552_ok : Node.check D_R22222 T2552 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2553_ok T2558_ok
def T2551 : Node := Node.leaf L2551
theorem T2551_ok : Node.check D_R22222 T2551 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2551_ok
def T2550 : Node := Node.leaf L2550
theorem T2550_ok : Node.check D_R22222 T2550 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2550_ok
def T2549 : Node := Node.leaf L2549
theorem T2549_ok : Node.check D_R22222 T2549 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2549_ok
def T2548 : Node := Node.leaf L2548
theorem T2548_ok : Node.check D_R22222 T2548 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((3645/2048),(7695/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2548_ok
def T2547 : Node := Node.split 2 T2548 T2549
theorem T2547_ok : Node.check D_R22222 T2547 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2548_ok T2549_ok
def T2546 : Node := Node.split 1 T2547 T2550
theorem T2546_ok : Node.check D_R22222 T2546 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2547_ok T2550_ok
def T2545 : Node := Node.split 3 T2546 T2551
theorem T2545_ok : Node.check D_R22222 T2545 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2546_ok T2551_ok
def T2544 : Node := Node.split 0 T2545 T2552
theorem T2544_ok : Node.check D_R22222 T2544 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2545_ok T2552_ok
def T2543 : Node := Node.leaf L2543
theorem T2543_ok : Node.check D_R22222 T2543 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((405/256),(3645/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2543_ok
def T2542 : Node := Node.split 2 T2543 T2544
theorem T2542_ok : Node.check D_R22222 T2542 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2543_ok T2544_ok
def T2541 : Node := Node.leaf L2541
theorem T2541_ok : Node.check D_R22222 T2541 [((1467/512),(815/256)),((405/512),(2025/2048)),((405/256),(2025/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2541_ok
def T2540 : Node := Node.split 1 T2541 T2542
theorem T2540_ok : Node.check D_R22222 T2540 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2541_ok T2542_ok
def T2539 : Node := Node.leaf L2539
theorem T2539_ok : Node.check D_R22222 T2539 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2539_ok
def T2538 : Node := Node.split 3 T2539 T2540
theorem T2538_ok : Node.check D_R22222 T2538 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2539_ok T2540_ok
def T2537 : Node := Node.leaf L2537
theorem T2537_ok : Node.check D_R22222 T2537 [((163/64),(1467/512)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2537_ok
def T2536 : Node := Node.split 0 T2537 T2538
theorem T2536_ok : Node.check D_R22222 T2536 [((163/64),(815/256)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2537_ok T2538_ok
def T2535 : Node := Node.split 2 T2536 T2559
theorem T2535_ok : Node.check D_R22222 T2535 [((163/64),(815/256)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2536_ok T2559_ok
def T2534 : Node := Node.split 1 T2535 T2592
theorem T2534_ok : Node.check D_R22222 T2534 [((163/64),(815/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2535_ok T2592_ok
def T2533 : Node := Node.leaf L2533
theorem T2533_ok : Node.check D_R22222 T2533 [((163/64),(815/256)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2533_ok
def T2532 : Node := Node.split 3 T2533 T2534
theorem T2532_ok : Node.check D_R22222 T2532 [((163/64),(815/256)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2533_ok T2534_ok
def T2531 : Node := Node.split 0 T2532 T2593
theorem T2531_ok : Node.check D_R22222 T2531 [((163/64),(489/128)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2532_ok T2593_ok
def T2530 : Node := Node.split 2 T2531 T2600
theorem T2530_ok : Node.check D_R22222 T2530 [((163/64),(489/128)),((405/512),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2531_ok T2600_ok
def T2529 : Node := Node.leaf L2529
theorem T2529_ok : Node.check D_R22222 T2529 [((163/64),(489/128)),((0),(405/512)),((405/256),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2529_ok
def T2528 : Node := Node.split 1 T2529 T2530
theorem T2528_ok : Node.check D_R22222 T2528 [((163/64),(489/128)),((0),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2529_ok T2530_ok
def T2527 : Node := Node.split 3 T2528 T2611
theorem T2527_ok : Node.check D_R22222 T2527 [((163/64),(489/128)),((0),(405/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2528_ok T2611_ok
def T2526 : Node := Node.split 0 T2527 T2658
theorem T2526_ok : Node.check D_R22222 T2526 [((163/64),(163/32)),((0),(405/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2527_ok T2658_ok
def T2525 : Node := Node.leaf L2525
theorem T2525_ok : Node.check D_R22222 T2525 [((1141/256),(163/32)),((1215/1024),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2525_ok
def T2524 : Node := Node.leaf L2524
theorem T2524_ok : Node.check D_R22222 T2524 [((1141/256),(163/32)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2524_ok
def T2523 : Node := Node.leaf L2523
theorem T2523_ok : Node.check D_R22222 T2523 [((2445/512),(163/32)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2523_ok
def T2522 : Node := Node.leaf L2522
theorem T2522_ok : Node.check D_R22222 T2522 [((1141/256),(2445/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2522_ok
def T2521 : Node := Node.split 0 T2522 T2523
theorem T2521_ok : Node.check D_R22222 T2521 [((1141/256),(163/32)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2522_ok T2523_ok
def T2520 : Node := Node.split 2 T2521 T2524
theorem T2520_ok : Node.check D_R22222 T2520 [((1141/256),(163/32)),((405/512),(1215/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2521_ok T2524_ok
def T2519 : Node := Node.split 1 T2520 T2525
theorem T2519_ok : Node.check D_R22222 T2519 [((1141/256),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2520_ok T2525_ok
def T2518 : Node := Node.leaf L2518
theorem T2518_ok : Node.check D_R22222 T2518 [((1141/256),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2518_ok
def T2517 : Node := Node.split 3 T2518 T2519
theorem T2517_ok : Node.check D_R22222 T2517 [((1141/256),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2518_ok T2519_ok
def T2516 : Node := Node.leaf L2516
theorem T2516_ok : Node.check D_R22222 T2516 [((489/128),(1141/256)),((1215/1024),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2516_ok
def T2515 : Node := Node.leaf L2515
theorem T2515_ok : Node.check D_R22222 T2515 [((489/128),(1141/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2515_ok
def T2514 : Node := Node.leaf L2514
theorem T2514_ok : Node.check D_R22222 T2514 [((2119/512),(1141/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L2514_ok
def T2513 : Node := Node.leaf L2513
theorem T2513_ok : Node.check D_R22222 T2513 [((2119/512),(1141/256)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2513_ok
def T2512 : Node := Node.leaf L2512
theorem T2512_ok : Node.check D_R22222 T2512 [((2119/512),(1141/256)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2512_ok
def T2511 : Node := Node.split 1 T2512 T2513
theorem T2511_ok : Node.check D_R22222 T2511 [((2119/512),(1141/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2512_ok T2513_ok
def T2510 : Node := Node.split 3 T2511 T2514
theorem T2510_ok : Node.check D_R22222 T2510 [((2119/512),(1141/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2511_ok T2514_ok
def T2509 : Node := Node.leaf L2509
theorem T2509_ok : Node.check D_R22222 T2509 [((489/128),(2119/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L2509_ok
def T2508 : Node := Node.leaf L2508
theorem T2508_ok : Node.check D_R22222 T2508 [((4075/1024),(2119/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2508_ok
def T2507 : Node := Node.leaf L2507
theorem T2507_ok : Node.check D_R22222 T2507 [((4075/1024),(2119/512)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2507_ok
def T2506 : Node := Node.leaf L2506
theorem T2506_ok : Node.check D_R22222 T2506 [((4075/1024),(2119/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2506_ok
def T2505 : Node := Node.split 2 T2506 T2507
theorem T2505_ok : Node.check D_R22222 T2505 [((4075/1024),(2119/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2506_ok T2507_ok
def T2504 : Node := Node.split 1 T2505 T2508
theorem T2504_ok : Node.check D_R22222 T2504 [((4075/1024),(2119/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2505_ok T2508_ok
def T2503 : Node := Node.leaf L2503
theorem T2503_ok : Node.check D_R22222 T2503 [((4075/1024),(2119/512)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2503_ok
def T2502 : Node := Node.leaf L2502
theorem T2502_ok : Node.check D_R22222 T2502 [((4075/1024),(2119/512)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2502_ok
def T2501 : Node := Node.split 2 T2502 T2503
theorem T2501_ok : Node.check D_R22222 T2501 [((4075/1024),(2119/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2502_ok T2503_ok
def T2500 : Node := Node.leaf L2500
theorem T2500_ok : Node.check D_R22222 T2500 [((4075/1024),(2119/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2500_ok
def T2499 : Node := Node.split 1 T2500 T2501
theorem T2499_ok : Node.check D_R22222 T2499 [((4075/1024),(2119/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2500_ok T2501_ok
def T2498 : Node := Node.split 3 T2499 T2504
theorem T2498_ok : Node.check D_R22222 T2498 [((4075/1024),(2119/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2499_ok T2504_ok
def T2497 : Node := Node.leaf L2497
theorem T2497_ok : Node.check D_R22222 T2497 [((489/128),(4075/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2497_ok
def T2496 : Node := Node.leaf L2496
theorem T2496_ok : Node.check D_R22222 T2496 [((489/128),(4075/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2496_ok
def T2495 : Node := Node.split 1 T2496 T2497
theorem T2495_ok : Node.check D_R22222 T2495 [((489/128),(4075/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2496_ok T2497_ok
def T2494 : Node := Node.leaf L2494
theorem T2494_ok : Node.check D_R22222 T2494 [((489/128),(4075/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2494_ok
def T2493 : Node := Node.leaf L2493
theorem T2493_ok : Node.check D_R22222 T2493 [((489/128),(4075/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2493_ok
def T2492 : Node := Node.split 2 T2493 T2494
theorem T2492_ok : Node.check D_R22222 T2492 [((489/128),(4075/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2493_ok T2494_ok
def T2491 : Node := Node.leaf L2491
theorem T2491_ok : Node.check D_R22222 T2491 [((489/128),(4075/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2491_ok
def T2490 : Node := Node.split 1 T2491 T2492
theorem T2490_ok : Node.check D_R22222 T2490 [((489/128),(4075/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2491_ok T2492_ok
def T2489 : Node := Node.split 3 T2490 T2495
theorem T2489_ok : Node.check D_R22222 T2489 [((489/128),(4075/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2490_ok T2495_ok
def T2488 : Node := Node.split 0 T2489 T2498
theorem T2488_ok : Node.check D_R22222 T2488 [((489/128),(2119/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2489_ok T2498_ok
def T2487 : Node := Node.leaf L2487
theorem T2487_ok : Node.check D_R22222 T2487 [((489/128),(2119/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2487_ok
def T2486 : Node := Node.split 2 T2487 T2488
theorem T2486_ok : Node.check D_R22222 T2486 [((489/128),(2119/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2487_ok T2488_ok
def T2485 : Node := Node.leaf L2485
theorem T2485_ok : Node.check D_R22222 T2485 [((489/128),(2119/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2485_ok
def T2484 : Node := Node.split 1 T2485 T2486
theorem T2484_ok : Node.check D_R22222 T2484 [((489/128),(2119/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2485_ok T2486_ok
def T2483 : Node := Node.split 3 T2484 T2509
theorem T2483_ok : Node.check D_R22222 T2483 [((489/128),(2119/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2484_ok T2509_ok
def T2482 : Node := Node.split 0 T2483 T2510
theorem T2482_ok : Node.check D_R22222 T2482 [((489/128),(1141/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2483_ok T2510_ok
def T2481 : Node := Node.split 2 T2482 T2515
theorem T2481_ok : Node.check D_R22222 T2481 [((489/128),(1141/256)),((405/512),(1215/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2482_ok T2515_ok
def T2480 : Node := Node.split 1 T2481 T2516
theorem T2480_ok : Node.check D_R22222 T2480 [((489/128),(1141/256)),((405/512),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2481_ok T2516_ok
def T2479 : Node := Node.leaf L2479
theorem T2479_ok : Node.check D_R22222 T2479 [((489/128),(1141/256)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2479_ok
def T2478 : Node := Node.split 3 T2479 T2480
theorem T2478_ok : Node.check D_R22222 T2478 [((489/128),(1141/256)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2479_ok T2480_ok
def T2477 : Node := Node.split 0 T2478 T2517
theorem T2477_ok : Node.check D_R22222 T2477 [((489/128),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2478_ok T2517_ok
def T2476 : Node := Node.leaf L2476
theorem T2476_ok : Node.check D_R22222 T2476 [((489/128),(163/32)),((405/512),(405/256)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2476_ok
def T2475 : Node := Node.split 2 T2476 T2477
theorem T2475_ok : Node.check D_R22222 T2475 [((489/128),(163/32)),((405/512),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2476_ok T2477_ok
def T2474 : Node := Node.leaf L2474
theorem T2474_ok : Node.check D_R22222 T2474 [((489/128),(163/32)),((0),(405/512)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2474_ok
def T2473 : Node := Node.split 1 T2474 T2475
theorem T2473_ok : Node.check D_R22222 T2473 [((489/128),(163/32)),((0),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2474_ok T2475_ok
def T2472 : Node := Node.leaf L2472
theorem T2472_ok : Node.check D_R22222 T2472 [((1141/256),(163/32)),((1215/1024),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2472_ok
def T2471 : Node := Node.leaf L2471
theorem T2471_ok : Node.check D_R22222 T2471 [((1141/256),(163/32)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2471_ok
def T2470 : Node := Node.leaf L2470
theorem T2470_ok : Node.check D_R22222 T2470 [((5053/1024),(163/32)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2470_ok
def T2469 : Node := Node.leaf L2469
theorem T2469_ok : Node.check D_R22222 T2469 [((5053/1024),(163/32)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2469_ok
def T2468 : Node := Node.leaf L2468
theorem T2468_ok : Node.check D_R22222 T2468 [((5053/1024),(163/32)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2468_ok
def T2467 : Node := Node.split 2 T2468 T2469
theorem T2467_ok : Node.check D_R22222 T2467 [((5053/1024),(163/32)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2468_ok T2469_ok
def T2466 : Node := Node.leaf L2466
theorem T2466_ok : Node.check D_R22222 T2466 [((5053/1024),(163/32)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2466_ok
def T2465 : Node := Node.leaf L2465
theorem T2465_ok : Node.check D_R22222 T2465 [((5053/1024),(163/32)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2465_ok
def T2464 : Node := Node.split 2 T2465 T2466
theorem T2464_ok : Node.check D_R22222 T2464 [((5053/1024),(163/32)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2465_ok T2466_ok
def T2463 : Node := Node.split 1 T2464 T2467
theorem T2463_ok : Node.check D_R22222 T2463 [((5053/1024),(163/32)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2464_ok T2467_ok
def T2462 : Node := Node.split 3 T2463 T2470
theorem T2462_ok : Node.check D_R22222 T2462 [((5053/1024),(163/32)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2463_ok T2470_ok
def T2461 : Node := Node.leaf L2461
theorem T2461_ok : Node.check D_R22222 T2461 [((2445/512),(5053/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2461_ok
def T2460 : Node := Node.leaf L2460
theorem T2460_ok : Node.check D_R22222 T2460 [((2445/512),(5053/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2460_ok
def T2459 : Node := Node.leaf L2459
theorem T2459_ok : Node.check D_R22222 T2459 [((2445/512),(5053/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2459_ok
def T2458 : Node := Node.split 2 T2459 T2460
theorem T2458_ok : Node.check D_R22222 T2458 [((2445/512),(5053/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2459_ok T2460_ok
def T2457 : Node := Node.leaf L2457
theorem T2457_ok : Node.check D_R22222 T2457 [((2445/512),(5053/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2457_ok
def T2456 : Node := Node.leaf L2456
theorem T2456_ok : Node.check D_R22222 T2456 [((2445/512),(5053/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2456_ok
def T2455 : Node := Node.split 2 T2456 T2457
theorem T2455_ok : Node.check D_R22222 T2455 [((2445/512),(5053/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2456_ok T2457_ok
def T2454 : Node := Node.split 1 T2455 T2458
theorem T2454_ok : Node.check D_R22222 T2454 [((2445/512),(5053/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2455_ok T2458_ok
def T2453 : Node := Node.split 3 T2454 T2461
theorem T2453_ok : Node.check D_R22222 T2453 [((2445/512),(5053/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2454_ok T2461_ok
def T2452 : Node := Node.split 0 T2453 T2462
theorem T2452_ok : Node.check D_R22222 T2452 [((2445/512),(163/32)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2453_ok T2462_ok
def T2451 : Node := Node.leaf L2451
theorem T2451_ok : Node.check D_R22222 T2451 [((2445/512),(163/32)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2451_ok
def T2450 : Node := Node.split 2 T2451 T2452
theorem T2450_ok : Node.check D_R22222 T2450 [((2445/512),(163/32)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2451_ok T2452_ok
def T2449 : Node := Node.leaf L2449
theorem T2449_ok : Node.check D_R22222 T2449 [((2445/512),(163/32)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2449_ok
def T2448 : Node := Node.split 1 T2449 T2450
theorem T2448_ok : Node.check D_R22222 T2448 [((2445/512),(163/32)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2449_ok T2450_ok
def T2447 : Node := Node.leaf L2447
theorem T2447_ok : Node.check D_R22222 T2447 [((2445/512),(163/32)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2447_ok
def T2446 : Node := Node.split 3 T2447 T2448
theorem T2446_ok : Node.check D_R22222 T2446 [((2445/512),(163/32)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2447_ok T2448_ok
def T2445 : Node := Node.leaf L2445
theorem T2445_ok : Node.check D_R22222 T2445 [((1141/256),(2445/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2445_ok
def T2444 : Node := Node.split 0 T2445 T2446
theorem T2444_ok : Node.check D_R22222 T2444 [((1141/256),(163/32)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2445_ok T2446_ok
def T2443 : Node := Node.split 2 T2444 T2471
theorem T2443_ok : Node.check D_R22222 T2443 [((1141/256),(163/32)),((405/512),(1215/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2444_ok T2471_ok
def T2442 : Node := Node.split 1 T2443 T2472
theorem T2442_ok : Node.check D_R22222 T2442 [((1141/256),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2443_ok T2472_ok
def T2441 : Node := Node.leaf L2441
theorem T2441_ok : Node.check D_R22222 T2441 [((1141/256),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2441_ok
def T2440 : Node := Node.split 3 T2441 T2442
theorem T2440_ok : Node.check D_R22222 T2440 [((1141/256),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2441_ok T2442_ok
def T2439 : Node := Node.leaf L2439
theorem T2439_ok : Node.check D_R22222 T2439 [((489/128),(1141/256)),((1215/1024),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2439_ok
def T2438 : Node := Node.leaf L2438
theorem T2438_ok : Node.check D_R22222 T2438 [((489/128),(1141/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2438_ok
def T2437 : Node := Node.leaf L2437
theorem T2437_ok : Node.check D_R22222 T2437 [((4401/1024),(1141/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2437_ok
def T2436 : Node := Node.leaf L2436
theorem T2436_ok : Node.check D_R22222 T2436 [((2119/512),(4401/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2436_ok
def T2435 : Node := Node.leaf L2435
theorem T2435_ok : Node.check D_R22222 T2435 [((2119/512),(4401/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2435_ok
def T2434 : Node := Node.leaf L2434
theorem T2434_ok : Node.check D_R22222 T2434 [((2119/512),(4401/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2434_ok
def T2433 : Node := Node.split 1 T2434 T2435
theorem T2433_ok : Node.check D_R22222 T2433 [((2119/512),(4401/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2434_ok T2435_ok
def T2432 : Node := Node.split 3 T2433 T2436
theorem T2432_ok : Node.check D_R22222 T2432 [((2119/512),(4401/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2433_ok T2436_ok
def T2431 : Node := Node.split 0 T2432 T2437
theorem T2431_ok : Node.check D_R22222 T2431 [((2119/512),(1141/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2432_ok T2437_ok
def T2430 : Node := Node.leaf L2430
theorem T2430_ok : Node.check D_R22222 T2430 [((2119/512),(1141/256)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2430_ok
def T2429 : Node := Node.split 2 T2430 T2431
theorem T2429_ok : Node.check D_R22222 T2429 [((2119/512),(1141/256)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2430_ok T2431_ok
def T2428 : Node := Node.leaf L2428
theorem T2428_ok : Node.check D_R22222 T2428 [((2119/512),(1141/256)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2428_ok
def T2427 : Node := Node.split 1 T2428 T2429
theorem T2427_ok : Node.check D_R22222 T2427 [((2119/512),(1141/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2428_ok T2429_ok
def T2426 : Node := Node.leaf L2426
theorem T2426_ok : Node.check D_R22222 T2426 [((2119/512),(1141/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2426_ok
def T2425 : Node := Node.split 3 T2426 T2427
theorem T2425_ok : Node.check D_R22222 T2425 [((2119/512),(1141/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2426_ok T2427_ok
def T2424 : Node := Node.leaf L2424
theorem T2424_ok : Node.check D_R22222 T2424 [((4075/1024),(2119/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2424_ok
def T2423 : Node := Node.leaf L2423
theorem T2423_ok : Node.check D_R22222 T2423 [((4075/1024),(2119/512)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2423_ok
def T2422 : Node := Node.leaf L2422
theorem T2422_ok : Node.check D_R22222 T2422 [((4075/1024),(2119/512)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2422_ok
def T2421 : Node := Node.split 2 T2422 T2423
theorem T2421_ok : Node.check D_R22222 T2421 [((4075/1024),(2119/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2422_ok T2423_ok
def T2420 : Node := Node.leaf L2420
theorem T2420_ok : Node.check D_R22222 T2420 [((4075/1024),(2119/512)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2420_ok
def T2419 : Node := Node.leaf L2419
theorem T2419_ok : Node.check D_R22222 T2419 [((4075/1024),(2119/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2419_ok
def T2418 : Node := Node.split 2 T2419 T2420
theorem T2418_ok : Node.check D_R22222 T2418 [((4075/1024),(2119/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2419_ok T2420_ok
def T2417 : Node := Node.split 1 T2418 T2421
theorem T2417_ok : Node.check D_R22222 T2417 [((4075/1024),(2119/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2418_ok T2421_ok
def T2416 : Node := Node.split 3 T2417 T2424
theorem T2416_ok : Node.check D_R22222 T2416 [((4075/1024),(2119/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2417_ok T2424_ok
def T2415 : Node := Node.leaf L2415
theorem T2415_ok : Node.check D_R22222 T2415 [((489/128),(4075/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2415_ok
def T2414 : Node := Node.leaf L2414
theorem T2414_ok : Node.check D_R22222 T2414 [((489/128),(4075/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2414_ok
def T2413 : Node := Node.leaf L2413
theorem T2413_ok : Node.check D_R22222 T2413 [((489/128),(4075/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2413_ok
def T2412 : Node := Node.split 2 T2413 T2414
theorem T2412_ok : Node.check D_R22222 T2412 [((489/128),(4075/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2413_ok T2414_ok
def T2411 : Node := Node.leaf L2411
theorem T2411_ok : Node.check D_R22222 T2411 [((489/128),(4075/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2411_ok
def T2410 : Node := Node.leaf L2410
theorem T2410_ok : Node.check D_R22222 T2410 [((489/128),(4075/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2410_ok
def T2409 : Node := Node.split 2 T2410 T2411
theorem T2409_ok : Node.check D_R22222 T2409 [((489/128),(4075/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2410_ok T2411_ok
def T2408 : Node := Node.split 1 T2409 T2412
theorem T2408_ok : Node.check D_R22222 T2408 [((489/128),(4075/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2409_ok T2412_ok
def T2407 : Node := Node.split 3 T2408 T2415
theorem T2407_ok : Node.check D_R22222 T2407 [((489/128),(4075/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2408_ok T2415_ok
def T2406 : Node := Node.split 0 T2407 T2416
theorem T2406_ok : Node.check D_R22222 T2406 [((489/128),(2119/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2407_ok T2416_ok
def T2405 : Node := Node.leaf L2405
theorem T2405_ok : Node.check D_R22222 T2405 [((489/128),(2119/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2405_ok
def T2404 : Node := Node.split 2 T2405 T2406
theorem T2404_ok : Node.check D_R22222 T2404 [((489/128),(2119/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2405_ok T2406_ok
def T2403 : Node := Node.leaf L2403
theorem T2403_ok : Node.check D_R22222 T2403 [((489/128),(2119/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2403_ok
def T2402 : Node := Node.split 1 T2403 T2404
theorem T2402_ok : Node.check D_R22222 T2402 [((489/128),(2119/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2403_ok T2404_ok
def T2401 : Node := Node.leaf L2401
theorem T2401_ok : Node.check D_R22222 T2401 [((489/128),(2119/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2401_ok
def T2400 : Node := Node.split 3 T2401 T2402
theorem T2400_ok : Node.check D_R22222 T2400 [((489/128),(2119/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2401_ok T2402_ok
def T2399 : Node := Node.split 0 T2400 T2425
theorem T2399_ok : Node.check D_R22222 T2399 [((489/128),(1141/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2400_ok T2425_ok
def T2398 : Node := Node.split 2 T2399 T2438
theorem T2398_ok : Node.check D_R22222 T2398 [((489/128),(1141/256)),((405/512),(1215/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2399_ok T2438_ok
def T2397 : Node := Node.split 1 T2398 T2439
theorem T2397_ok : Node.check D_R22222 T2397 [((489/128),(1141/256)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2398_ok T2439_ok
def T2396 : Node := Node.leaf L2396
theorem T2396_ok : Node.check D_R22222 T2396 [((489/128),(1141/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2396_ok
def T2395 : Node := Node.split 3 T2396 T2397
theorem T2395_ok : Node.check D_R22222 T2395 [((489/128),(1141/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2396_ok T2397_ok
def T2394 : Node := Node.split 0 T2395 T2440
theorem T2394_ok : Node.check D_R22222 T2394 [((489/128),(163/32)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2395_ok T2440_ok
def T2393 : Node := Node.leaf L2393
theorem T2393_ok : Node.check D_R22222 T2393 [((489/128),(163/32)),((405/512),(405/256)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2393_ok
def T2392 : Node := Node.split 2 T2393 T2394
theorem T2392_ok : Node.check D_R22222 T2392 [((489/128),(163/32)),((405/512),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2393_ok T2394_ok
def T2391 : Node := Node.leaf L2391
theorem T2391_ok : Node.check D_R22222 T2391 [((489/128),(163/32)),((0),(405/512)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2391_ok
def T2390 : Node := Node.split 1 T2391 T2392
theorem T2390_ok : Node.check D_R22222 T2390 [((489/128),(163/32)),((0),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2391_ok T2392_ok
def T2389 : Node := Node.split 3 T2390 T2473
theorem T2389_ok : Node.check D_R22222 T2389 [((489/128),(163/32)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2390_ok T2473_ok
def T2388 : Node := Node.leaf L2388
theorem T2388_ok : Node.check D_R22222 T2388 [((815/256),(489/128)),((1215/1024),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2388_ok
def T2387 : Node := Node.leaf L2387
theorem T2387_ok : Node.check D_R22222 T2387 [((815/256),(489/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2387_ok
def T2386 : Node := Node.leaf L2386
theorem T2386_ok : Node.check D_R22222 T2386 [((1793/512),(489/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2386_ok
def T2385 : Node := Node.leaf L2385
theorem T2385_ok : Node.check D_R22222 T2385 [((815/256),(1793/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L2385_ok
def T2384 : Node := Node.leaf L2384
theorem T2384_ok : Node.check D_R22222 T2384 [((815/256),(1793/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2384_ok
def T2383 : Node := Node.leaf L2383
theorem T2383_ok : Node.check D_R22222 T2383 [((815/256),(1793/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2383_ok
def T2382 : Node := Node.split 1 T2383 T2384
theorem T2382_ok : Node.check D_R22222 T2382 [((815/256),(1793/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2383_ok T2384_ok
def T2381 : Node := Node.split 3 T2382 T2385
theorem T2381_ok : Node.check D_R22222 T2381 [((815/256),(1793/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2382_ok T2385_ok
def T2380 : Node := Node.split 0 T2381 T2386
theorem T2380_ok : Node.check D_R22222 T2380 [((815/256),(489/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2381_ok T2386_ok
def T2379 : Node := Node.split 2 T2380 T2387
theorem T2379_ok : Node.check D_R22222 T2379 [((815/256),(489/128)),((405/512),(1215/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2380_ok T2387_ok
def T2378 : Node := Node.split 1 T2379 T2388
theorem T2378_ok : Node.check D_R22222 T2378 [((815/256),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2379_ok T2388_ok
def T2377 : Node := Node.leaf L2377
theorem T2377_ok : Node.check D_R22222 T2377 [((815/256),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2377_ok
def T2376 : Node := Node.split 3 T2377 T2378
theorem T2376_ok : Node.check D_R22222 T2376 [((815/256),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2377_ok T2378_ok
def T2375 : Node := Node.leaf L2375
theorem T2375_ok : Node.check D_R22222 T2375 [((163/64),(815/256)),((1215/1024),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2375_ok
def T2374 : Node := Node.leaf L2374
theorem T2374_ok : Node.check D_R22222 T2374 [((163/64),(815/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L2374_ok
def T2373 : Node := Node.leaf L2373
theorem T2373_ok : Node.check D_R22222 T2373 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L2373_ok
def T2372 : Node := Node.leaf L2372
theorem T2372_ok : Node.check D_R22222 T2372 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2372_ok
def T2371 : Node := Node.leaf L2371
theorem T2371_ok : Node.check D_R22222 T2371 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2371_ok
def T2370 : Node := Node.leaf L2370
theorem T2370_ok : Node.check D_R22222 T2370 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2370_ok
def T2369 : Node := Node.split 2 T2370 T2371
theorem T2369_ok : Node.check D_R22222 T2369 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2370_ok T2371_ok
def T2368 : Node := Node.split 1 T2369 T2372
theorem T2368_ok : Node.check D_R22222 T2368 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2369_ok T2372_ok
def T2367 : Node := Node.leaf L2367
theorem T2367_ok : Node.check D_R22222 T2367 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2367_ok
def T2366 : Node := Node.leaf L2366
theorem T2366_ok : Node.check D_R22222 T2366 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2366_ok
def T2365 : Node := Node.split 2 T2366 T2367
theorem T2365_ok : Node.check D_R22222 T2365 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2366_ok T2367_ok
def T2364 : Node := Node.leaf L2364
theorem T2364_ok : Node.check D_R22222 T2364 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2364_ok
def T2363 : Node := Node.leaf L2363
theorem T2363_ok : Node.check D_R22222 T2363 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2363_ok
def T2362 : Node := Node.split 2 T2363 T2364
theorem T2362_ok : Node.check D_R22222 T2362 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2363_ok T2364_ok
def T2361 : Node := Node.split 1 T2362 T2365
theorem T2361_ok : Node.check D_R22222 T2361 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2362_ok T2365_ok
def T2360 : Node := Node.split 3 T2361 T2368
theorem T2360_ok : Node.check D_R22222 T2360 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2361_ok T2368_ok
def T2359 : Node := Node.leaf L2359
theorem T2359_ok : Node.check D_R22222 T2359 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2359_ok
def T2358 : Node := Node.leaf L2358
theorem T2358_ok : Node.check D_R22222 T2358 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2358_ok
def T2357 : Node := Node.leaf L2357
theorem T2357_ok : Node.check D_R22222 T2357 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2357_ok
def T2356 : Node := Node.split 2 T2357 T2358
theorem T2356_ok : Node.check D_R22222 T2356 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2357_ok T2358_ok
def T2355 : Node := Node.split 1 T2356 T2359
theorem T2355_ok : Node.check D_R22222 T2355 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2356_ok T2359_ok
def T2354 : Node := Node.leaf L2354
theorem T2354_ok : Node.check D_R22222 T2354 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2354_ok
def T2353 : Node := Node.leaf L2353
theorem T2353_ok : Node.check D_R22222 T2353 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2353_ok
def T2352 : Node := Node.split 2 T2353 T2354
theorem T2352_ok : Node.check D_R22222 T2352 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2353_ok T2354_ok
def T2351 : Node := Node.leaf L2351
theorem T2351_ok : Node.check D_R22222 T2351 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2351_ok
def T2350 : Node := Node.leaf L2350
theorem T2350_ok : Node.check D_R22222 T2350 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2350_ok
def T2349 : Node := Node.split 2 T2350 T2351
theorem T2349_ok : Node.check D_R22222 T2349 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2350_ok T2351_ok
def T2348 : Node := Node.split 1 T2349 T2352
theorem T2348_ok : Node.check D_R22222 T2348 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2349_ok T2352_ok
def T2347 : Node := Node.split 3 T2348 T2355
theorem T2347_ok : Node.check D_R22222 T2347 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2348_ok T2355_ok
def T2346 : Node := Node.split 0 T2347 T2360
theorem T2346_ok : Node.check D_R22222 T2346 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2347_ok T2360_ok
def T2345 : Node := Node.leaf L2345
theorem T2345_ok : Node.check D_R22222 T2345 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2345_ok
def T2344 : Node := Node.split 2 T2345 T2346
theorem T2344_ok : Node.check D_R22222 T2344 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2345_ok T2346_ok
def T2343 : Node := Node.leaf L2343
theorem T2343_ok : Node.check D_R22222 T2343 [((1467/512),(815/256)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2343_ok
def T2342 : Node := Node.split 1 T2343 T2344
theorem T2342_ok : Node.check D_R22222 T2342 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2343_ok T2344_ok
def T2341 : Node := Node.split 3 T2342 T2373
theorem T2341_ok : Node.check D_R22222 T2341 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2342_ok T2373_ok
def T2340 : Node := Node.leaf L2340
theorem T2340_ok : Node.check D_R22222 T2340 [((163/64),(1467/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L2340_ok
def T2339 : Node := Node.leaf L2339
theorem T2339_ok : Node.check D_R22222 T2339 [((2771/1024),(1467/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L2339_ok
def T2338 : Node := Node.leaf L2338
theorem T2338_ok : Node.check D_R22222 T2338 [((2771/1024),(1467/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2338_ok
def T2337 : Node := Node.leaf L2337
theorem T2337_ok : Node.check D_R22222 T2337 [((2771/1024),(1467/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L2337_ok
def T2336 : Node := Node.split 1 T2337 T2338
theorem T2336_ok : Node.check D_R22222 T2336 [((2771/1024),(1467/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2337_ok T2338_ok
def T2335 : Node := Node.split 3 T2336 T2339
theorem T2335_ok : Node.check D_R22222 T2335 [((2771/1024),(1467/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2336_ok T2339_ok
def T2334 : Node := Node.leaf L2334
theorem T2334_ok : Node.check D_R22222 T2334 [((163/64),(2771/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2334_ok
def T2333 : Node := Node.split 0 T2334 T2335
theorem T2333_ok : Node.check D_R22222 T2333 [((163/64),(1467/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2334_ok T2335_ok
def T2332 : Node := Node.leaf L2332
theorem T2332_ok : Node.check D_R22222 T2332 [((163/64),(1467/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2332_ok
def T2331 : Node := Node.split 2 T2332 T2333
theorem T2331_ok : Node.check D_R22222 T2331 [((163/64),(1467/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2332_ok T2333_ok
def T2330 : Node := Node.leaf L2330
theorem T2330_ok : Node.check D_R22222 T2330 [((163/64),(1467/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L2330_ok
def T2329 : Node := Node.split 1 T2330 T2331
theorem T2329_ok : Node.check D_R22222 T2329 [((163/64),(1467/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2330_ok T2331_ok
def T2328 : Node := Node.split 3 T2329 T2340
theorem T2328_ok : Node.check D_R22222 T2328 [((163/64),(1467/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2329_ok T2340_ok
def T2327 : Node := Node.split 0 T2328 T2341
theorem T2327_ok : Node.check D_R22222 T2327 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2328_ok T2341_ok
def T2326 : Node := Node.split 2 T2327 T2374
theorem T2326_ok : Node.check D_R22222 T2326 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2327_ok T2374_ok
def T2325 : Node := Node.split 1 T2326 T2375
theorem T2325_ok : Node.check D_R22222 T2325 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2326_ok T2375_ok
def T2324 : Node := Node.leaf L2324
theorem T2324_ok : Node.check D_R22222 T2324 [((163/64),(815/256)),((1215/1024),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2324_ok
def T2323 : Node := Node.leaf L2323
theorem T2323_ok : Node.check D_R22222 T2323 [((163/64),(815/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2323_ok
def T2322 : Node := Node.leaf L2322
theorem T2322_ok : Node.check D_R22222 T2322 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2322_ok
def T2321 : Node := Node.leaf L2321
theorem T2321_ok : Node.check D_R22222 T2321 [((163/64),(1467/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L2321_ok
def T2320 : Node := Node.split 0 T2321 T2322
theorem T2320_ok : Node.check D_R22222 T2320 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2321_ok T2322_ok
def T2319 : Node := Node.split 2 T2320 T2323
theorem T2319_ok : Node.check D_R22222 T2319 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2320_ok T2323_ok
def T2318 : Node := Node.split 1 T2319 T2324
theorem T2318_ok : Node.check D_R22222 T2318 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2319_ok T2324_ok
def T2317 : Node := Node.split 3 T2318 T2325
theorem T2317_ok : Node.check D_R22222 T2317 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2318_ok T2325_ok
def T2316 : Node := Node.split 0 T2317 T2376
theorem T2316_ok : Node.check D_R22222 T2316 [((163/64),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2317_ok T2376_ok
def T2315 : Node := Node.leaf L2315
theorem T2315_ok : Node.check D_R22222 T2315 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2315_ok
def T2314 : Node := Node.split 2 T2315 T2316
theorem T2314_ok : Node.check D_R22222 T2314 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2315_ok T2316_ok
def T2313 : Node := Node.leaf L2313
theorem T2313_ok : Node.check D_R22222 T2313 [((163/64),(489/128)),((0),(405/512)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L2313_ok
def T2312 : Node := Node.split 1 T2313 T2314
theorem T2312_ok : Node.check D_R22222 T2312 [((163/64),(489/128)),((0),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2313_ok T2314_ok
def T2311 : Node := Node.leaf L2311
theorem T2311_ok : Node.check D_R22222 T2311 [((815/256),(489/128)),((1215/1024),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2311_ok
def T2310 : Node := Node.leaf L2310
theorem T2310_ok : Node.check D_R22222 T2310 [((815/256),(489/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2310_ok
def T2309 : Node := Node.leaf L2309
theorem T2309_ok : Node.check D_R22222 T2309 [((3749/1024),(489/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2309_ok
def T2308 : Node := Node.leaf L2308
theorem T2308_ok : Node.check D_R22222 T2308 [((3749/1024),(489/128)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2308_ok
def T2307 : Node := Node.leaf L2307
theorem T2307_ok : Node.check D_R22222 T2307 [((3749/1024),(489/128)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2307_ok
def T2306 : Node := Node.split 1 T2307 T2308
theorem T2306_ok : Node.check D_R22222 T2306 [((3749/1024),(489/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2307_ok T2308_ok
def T2305 : Node := Node.split 3 T2306 T2309
theorem T2305_ok : Node.check D_R22222 T2305 [((3749/1024),(489/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2306_ok T2309_ok
def T2304 : Node := Node.leaf L2304
theorem T2304_ok : Node.check D_R22222 T2304 [((1793/512),(3749/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2304_ok
def T2303 : Node := Node.split 0 T2304 T2305
theorem T2303_ok : Node.check D_R22222 T2303 [((1793/512),(489/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2304_ok T2305_ok
def T2302 : Node := Node.leaf L2302
theorem T2302_ok : Node.check D_R22222 T2302 [((1793/512),(489/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2302_ok
def T2301 : Node := Node.split 2 T2302 T2303
theorem T2301_ok : Node.check D_R22222 T2301 [((1793/512),(489/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2302_ok T2303_ok
def T2300 : Node := Node.leaf L2300
theorem T2300_ok : Node.check D_R22222 T2300 [((1793/512),(489/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2300_ok
def T2299 : Node := Node.split 1 T2300 T2301
theorem T2299_ok : Node.check D_R22222 T2299 [((1793/512),(489/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2300_ok T2301_ok
def T2298 : Node := Node.leaf L2298
theorem T2298_ok : Node.check D_R22222 T2298 [((1793/512),(489/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2298_ok
def T2297 : Node := Node.split 3 T2298 T2299
theorem T2297_ok : Node.check D_R22222 T2297 [((1793/512),(489/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2298_ok T2299_ok
def T2296 : Node := Node.leaf L2296
theorem T2296_ok : Node.check D_R22222 T2296 [((815/256),(1793/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2296_ok
def T2295 : Node := Node.leaf L2295
theorem T2295_ok : Node.check D_R22222 T2295 [((815/256),(1793/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2295_ok
def T2294 : Node := Node.split 2 T2295 T2296
theorem T2294_ok : Node.check D_R22222 T2294 [((815/256),(1793/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2295_ok T2296_ok
def T2293 : Node := Node.leaf L2293
theorem T2293_ok : Node.check D_R22222 T2293 [((815/256),(1793/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2293_ok
def T2292 : Node := Node.split 1 T2293 T2294
theorem T2292_ok : Node.check D_R22222 T2292 [((815/256),(1793/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2293_ok T2294_ok
def T2291 : Node := Node.leaf L2291
theorem T2291_ok : Node.check D_R22222 T2291 [((815/256),(1793/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2291_ok
def T2290 : Node := Node.split 3 T2291 T2292
theorem T2290_ok : Node.check D_R22222 T2290 [((815/256),(1793/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2291_ok T2292_ok
def T2289 : Node := Node.split 0 T2290 T2297
theorem T2289_ok : Node.check D_R22222 T2289 [((815/256),(489/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2290_ok T2297_ok
def T2288 : Node := Node.split 2 T2289 T2310
theorem T2288_ok : Node.check D_R22222 T2288 [((815/256),(489/128)),((405/512),(1215/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2289_ok T2310_ok
def T2287 : Node := Node.split 1 T2288 T2311
theorem T2287_ok : Node.check D_R22222 T2287 [((815/256),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2288_ok T2311_ok
def T2286 : Node := Node.leaf L2286
theorem T2286_ok : Node.check D_R22222 T2286 [((815/256),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2286_ok
def T2285 : Node := Node.split 3 T2286 T2287
theorem T2285_ok : Node.check D_R22222 T2285 [((815/256),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2286_ok T2287_ok
def T2284 : Node := Node.leaf L2284
theorem T2284_ok : Node.check D_R22222 T2284 [((163/64),(815/256)),((1215/1024),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2284_ok
def T2283 : Node := Node.leaf L2283
theorem T2283_ok : Node.check D_R22222 T2283 [((163/64),(815/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L2283_ok
def T2282 : Node := Node.leaf L2282
theorem T2282_ok : Node.check D_R22222 T2282 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2282_ok
def T2281 : Node := Node.leaf L2281
theorem T2281_ok : Node.check D_R22222 T2281 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2281_ok
def T2280 : Node := Node.leaf L2280
theorem T2280_ok : Node.check D_R22222 T2280 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2280_ok
def T2279 : Node := Node.split 2 T2280 T2281
theorem T2279_ok : Node.check D_R22222 T2279 [((3097/1024),(815/256)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2280_ok T2281_ok
def T2278 : Node := Node.leaf L2278
theorem T2278_ok : Node.check D_R22222 T2278 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2278_ok
def T2277 : Node := Node.leaf L2277
theorem T2277_ok : Node.check D_R22222 T2277 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2277_ok
def T2276 : Node := Node.split 2 T2277 T2278
theorem T2276_ok : Node.check D_R22222 T2276 [((3097/1024),(815/256)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2277_ok T2278_ok
def T2275 : Node := Node.split 1 T2276 T2279
theorem T2275_ok : Node.check D_R22222 T2275 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2276_ok T2279_ok
def T2274 : Node := Node.split 3 T2275 T2282
theorem T2274_ok : Node.check D_R22222 T2274 [((3097/1024),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2275_ok T2282_ok
def T2273 : Node := Node.leaf L2273
theorem T2273_ok : Node.check D_R22222 T2273 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2273_ok
def T2272 : Node := Node.leaf L2272
theorem T2272_ok : Node.check D_R22222 T2272 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2272_ok
def T2271 : Node := Node.leaf L2271
theorem T2271_ok : Node.check D_R22222 T2271 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2271_ok
def T2270 : Node := Node.split 2 T2271 T2272
theorem T2270_ok : Node.check D_R22222 T2270 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2271_ok T2272_ok
def T2269 : Node := Node.split 1 T2270 T2273
theorem T2269_ok : Node.check D_R22222 T2269 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2270_ok T2273_ok
def T2268 : Node := Node.leaf L2268
theorem T2268_ok : Node.check D_R22222 T2268 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2268_ok
def T2267 : Node := Node.leaf L2267
theorem T2267_ok : Node.check D_R22222 T2267 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2267_ok
def T2266 : Node := Node.split 2 T2267 T2268
theorem T2266_ok : Node.check D_R22222 T2266 [((1467/512),(3097/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2267_ok T2268_ok
def T2265 : Node := Node.leaf L2265
theorem T2265_ok : Node.check D_R22222 T2265 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2265_ok
def T2264 : Node := Node.leaf L2264
theorem T2264_ok : Node.check D_R22222 T2264 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2264_ok
def T2263 : Node := Node.split 2 T2264 T2265
theorem T2263_ok : Node.check D_R22222 T2263 [((1467/512),(3097/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2264_ok T2265_ok
def T2262 : Node := Node.split 1 T2263 T2266
theorem T2262_ok : Node.check D_R22222 T2262 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2263_ok T2266_ok
def T2261 : Node := Node.split 3 T2262 T2269
theorem T2261_ok : Node.check D_R22222 T2261 [((1467/512),(3097/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2262_ok T2269_ok
def T2260 : Node := Node.split 0 T2261 T2274
theorem T2260_ok : Node.check D_R22222 T2260 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2261_ok T2274_ok
def T2259 : Node := Node.leaf L2259
theorem T2259_ok : Node.check D_R22222 T2259 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2259_ok
def T2258 : Node := Node.split 2 T2259 T2260
theorem T2258_ok : Node.check D_R22222 T2258 [((1467/512),(815/256)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2259_ok T2260_ok
def T2257 : Node := Node.leaf L2257
theorem T2257_ok : Node.check D_R22222 T2257 [((1467/512),(815/256)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2257_ok
def T2256 : Node := Node.split 1 T2257 T2258
theorem T2256_ok : Node.check D_R22222 T2256 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2257_ok T2258_ok
def T2255 : Node := Node.leaf L2255
theorem T2255_ok : Node.check D_R22222 T2255 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2255_ok
def T2254 : Node := Node.split 3 T2255 T2256
theorem T2254_ok : Node.check D_R22222 T2254 [((1467/512),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2255_ok T2256_ok
def T2253 : Node := Node.leaf L2253
theorem T2253_ok : Node.check D_R22222 T2253 [((2771/1024),(1467/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L2253_ok
def T2252 : Node := Node.leaf L2252
theorem T2252_ok : Node.check D_R22222 T2252 [((2771/1024),(1467/512)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2252_ok
def T2251 : Node := Node.leaf L2251
theorem T2251_ok : Node.check D_R22222 T2251 [((2771/1024),(1467/512)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2251_ok
def T2250 : Node := Node.split 2 T2251 T2252
theorem T2250_ok : Node.check D_R22222 T2250 [((2771/1024),(1467/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2251_ok T2252_ok
def T2249 : Node := Node.leaf L2249
theorem T2249_ok : Node.check D_R22222 T2249 [((2771/1024),(1467/512)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2249_ok
def T2248 : Node := Node.leaf L2248
theorem T2248_ok : Node.check D_R22222 T2248 [((2771/1024),(1467/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L2248_ok
def T2247 : Node := Node.split 2 T2248 T2249
theorem T2247_ok : Node.check D_R22222 T2247 [((2771/1024),(1467/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2248_ok T2249_ok
def T2246 : Node := Node.split 1 T2247 T2250
theorem T2246_ok : Node.check D_R22222 T2246 [((2771/1024),(1467/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2247_ok T2250_ok
def T2245 : Node := Node.split 3 T2246 T2253
theorem T2245_ok : Node.check D_R22222 T2245 [((2771/1024),(1467/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2246_ok T2253_ok
def T2244 : Node := Node.leaf L2244
theorem T2244_ok : Node.check D_R22222 T2244 [((163/64),(2771/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2244_ok
def T2243 : Node := Node.split 0 T2244 T2245
theorem T2243_ok : Node.check D_R22222 T2243 [((163/64),(1467/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2244_ok T2245_ok
def T2242 : Node := Node.leaf L2242
theorem T2242_ok : Node.check D_R22222 T2242 [((163/64),(1467/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2242_ok
def T2241 : Node := Node.split 2 T2242 T2243
theorem T2241_ok : Node.check D_R22222 T2241 [((163/64),(1467/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2242_ok T2243_ok
def T2240 : Node := Node.leaf L2240
theorem T2240_ok : Node.check D_R22222 T2240 [((163/64),(1467/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L2240_ok
def T2239 : Node := Node.split 1 T2240 T2241
theorem T2239_ok : Node.check D_R22222 T2239 [((163/64),(1467/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2240_ok T2241_ok
def T2238 : Node := Node.leaf L2238
theorem T2238_ok : Node.check D_R22222 T2238 [((163/64),(1467/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L2238_ok
def T2237 : Node := Node.split 3 T2238 T2239
theorem T2237_ok : Node.check D_R22222 T2237 [((163/64),(1467/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2238_ok T2239_ok
def T2236 : Node := Node.split 0 T2237 T2254
theorem T2236_ok : Node.check D_R22222 T2236 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2237_ok T2254_ok
def T2235 : Node := Node.split 2 T2236 T2283
theorem T2235_ok : Node.check D_R22222 T2235 [((163/64),(815/256)),((405/512),(1215/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2236_ok T2283_ok
def T2234 : Node := Node.split 1 T2235 T2284
theorem T2234_ok : Node.check D_R22222 T2234 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2235_ok T2284_ok
def T2233 : Node := Node.leaf L2233
theorem T2233_ok : Node.check D_R22222 T2233 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L2233_ok
def T2232 : Node := Node.split 3 T2233 T2234
theorem T2232_ok : Node.check D_R22222 T2232 [((163/64),(815/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2233_ok T2234_ok
def T2231 : Node := Node.split 0 T2232 T2285
theorem T2231_ok : Node.check D_R22222 T2231 [((163/64),(489/128)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2232_ok T2285_ok
def T2230 : Node := Node.leaf L2230
theorem T2230_ok : Node.check D_R22222 T2230 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2230_ok
def T2229 : Node := Node.split 2 T2230 T2231
theorem T2229_ok : Node.check D_R22222 T2229 [((163/64),(489/128)),((405/512),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2230_ok T2231_ok
def T2228 : Node := Node.leaf L2228
theorem T2228_ok : Node.check D_R22222 T2228 [((163/64),(489/128)),((0),(405/512)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L2228_ok
def T2227 : Node := Node.split 1 T2228 T2229
theorem T2227_ok : Node.check D_R22222 T2227 [((163/64),(489/128)),((0),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2228_ok T2229_ok
def T2226 : Node := Node.split 3 T2227 T2312
theorem T2226_ok : Node.check D_R22222 T2226 [((163/64),(489/128)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2227_ok T2312_ok
def T2225 : Node := Node.split 0 T2226 T2389
theorem T2225_ok : Node.check D_R22222 T2225 [((163/64),(163/32)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2226_ok T2389_ok
def T2224 : Node := Node.split 2 T2225 T2526
theorem T2224_ok : Node.check D_R22222 T2224 [((163/64),(163/32)),((0),(405/256)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2225_ok T2526_ok
def T2223 : Node := Node.split 1 T2224 T2723
theorem T2223_ok : Node.check D_R22222 T2223 [((163/64),(163/32)),((0),(405/128)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2224_ok T2723_ok
def T2222 : Node := Node.split 3 T2223 T2990
theorem T2222_ok : Node.check D_R22222 T2222 [((163/64),(163/32)),((0),(405/128)),((0),(405/128)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2223_ok T2990_ok
def T2221 : Node := Node.leaf L2221
theorem T2221_ok : Node.check D_R22222 T2221 [((163/128),(163/64)),((405/256),(405/128)),((405/256),(405/128)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2221_ok
def T2220 : Node := Node.leaf L2220
theorem T2220_ok : Node.check D_R22222 T2220 [((163/128),(163/64)),((1215/512),(405/128)),((405/256),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2220_ok
def T2219 : Node := Node.leaf L2219
theorem T2219_ok : Node.check D_R22222 T2219 [((163/128),(163/64)),((405/256),(1215/512)),((1215/512),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2219_ok
def T2218 : Node := Node.leaf L2218
theorem T2218_ok : Node.check D_R22222 T2218 [((489/256),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2218_ok
def T2217 : Node := Node.leaf L2217
theorem T2217_ok : Node.check D_R22222 T2217 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/256),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2217_ok
def T2216 : Node := Node.leaf L2216
theorem T2216_ok : Node.check D_R22222 T2216 [((489/256),(163/64)),((405/256),(2025/1024)),((405/256),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2216_ok
def T2215 : Node := Node.split 1 T2216 T2217
theorem T2215_ok : Node.check D_R22222 T2215 [((489/256),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2216_ok T2217_ok
def T2214 : Node := Node.split 3 T2215 T2218
theorem T2214_ok : Node.check D_R22222 T2214 [((489/256),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2215_ok T2218_ok
def T2213 : Node := Node.leaf L2213
theorem T2213_ok : Node.check D_R22222 T2213 [((163/128),(489/256)),((405/256),(1215/512)),((405/256),(1215/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2213_ok
def T2212 : Node := Node.split 0 T2213 T2214
theorem T2212_ok : Node.check D_R22222 T2212 [((163/128),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2213_ok T2214_ok
def T2211 : Node := Node.split 2 T2212 T2219
theorem T2211_ok : Node.check D_R22222 T2211 [((163/128),(163/64)),((405/256),(1215/512)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2212_ok T2219_ok
def T2210 : Node := Node.split 1 T2211 T2220
theorem T2210_ok : Node.check D_R22222 T2210 [((163/128),(163/64)),((405/256),(405/128)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2211_ok T2220_ok
def T2209 : Node := Node.split 3 T2210 T2221
theorem T2209_ok : Node.check D_R22222 T2209 [((163/128),(163/64)),((405/256),(405/128)),((405/256),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2210_ok T2221_ok
def T2208 : Node := Node.leaf L2208
theorem T2208_ok : Node.check D_R22222 T2208 [((0),(163/128)),((1215/512),(405/128)),((405/256),(405/128)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2208_ok
def T2207 : Node := Node.leaf L2207
theorem T2207_ok : Node.check D_R22222 T2207 [((0),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2207_ok
def T2206 : Node := Node.leaf L2206
theorem T2206_ok : Node.check D_R22222 T2206 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L2206_ok
def T2205 : Node := Node.leaf L2205
theorem T2205_ok : Node.check D_R22222 T2205 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/256),(1215/512)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L2205_ok
def T2204 : Node := Node.leaf L2204
theorem T2204_ok : Node.check D_R22222 T2204 [((163/256),(163/128)),((405/256),(2025/1024)),((405/256),(1215/512)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L2204_ok
def T2203 : Node := Node.split 1 T2204 T2205
theorem T2203_ok : Node.check D_R22222 T2203 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2204_ok T2205_ok
def T2202 : Node := Node.split 3 T2203 T2206
theorem T2202_ok : Node.check D_R22222 T2202 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2203_ok T2206_ok
def T2201 : Node := Node.leaf L2201
theorem T2201_ok : Node.check D_R22222 T2201 [((0),(163/256)),((405/256),(1215/512)),((405/256),(1215/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2201_ok
def T2200 : Node := Node.split 0 T2201 T2202
theorem T2200_ok : Node.check D_R22222 T2200 [((0),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2201_ok T2202_ok
def T2199 : Node := Node.split 2 T2200 T2207
theorem T2199_ok : Node.check D_R22222 T2199 [((0),(163/128)),((405/256),(1215/512)),((405/256),(405/128)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2200_ok T2207_ok
def T2198 : Node := Node.split 1 T2199 T2208
theorem T2198_ok : Node.check D_R22222 T2198 [((0),(163/128)),((405/256),(405/128)),((405/256),(405/128)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2199_ok T2208_ok
def T2197 : Node := Node.leaf L2197
theorem T2197_ok : Node.check D_R22222 T2197 [((0),(163/128)),((1215/512),(405/128)),((1215/512),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2197_ok
def T2196 : Node := Node.leaf L2196
theorem T2196_ok : Node.check D_R22222 T2196 [((163/256),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2196_ok
def T2195 : Node := Node.leaf L2195
theorem T2195_ok : Node.check D_R22222 T2195 [((163/256),(163/128)),((2835/1024),(405/128)),((405/256),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2195_ok
def T2194 : Node := Node.leaf L2194
theorem T2194_ok : Node.check D_R22222 T2194 [((163/256),(163/128)),((1215/512),(2835/1024)),((405/256),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2194_ok
def T2193 : Node := Node.split 1 T2194 T2195
theorem T2193_ok : Node.check D_R22222 T2193 [((163/256),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2194_ok T2195_ok
def T2192 : Node := Node.split 3 T2193 T2196
theorem T2192_ok : Node.check D_R22222 T2192 [((163/256),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2193_ok T2196_ok
def T2191 : Node := Node.leaf L2191
theorem T2191_ok : Node.check D_R22222 T2191 [((0),(163/256)),((1215/512),(405/128)),((405/256),(1215/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2191_ok
def T2190 : Node := Node.split 0 T2191 T2192
theorem T2190_ok : Node.check D_R22222 T2190 [((0),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2191_ok T2192_ok
def T2189 : Node := Node.split 2 T2190 T2197
theorem T2189_ok : Node.check D_R22222 T2189 [((0),(163/128)),((1215/512),(405/128)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2190_ok T2197_ok
def T2188 : Node := Node.leaf L2188
theorem T2188_ok : Node.check D_R22222 T2188 [((163/256),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2188_ok
def T2187 : Node := Node.leaf L2187
theorem T2187_ok : Node.check D_R22222 T2187 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/512),(405/128)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2187_ok
def T2186 : Node := Node.leaf L2186
theorem T2186_ok : Node.check D_R22222 T2186 [((163/256),(163/128)),((405/256),(2025/1024)),((1215/512),(405/128)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2186_ok
def T2185 : Node := Node.split 1 T2186 T2187
theorem T2185_ok : Node.check D_R22222 T2185 [((163/256),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2186_ok T2187_ok
def T2184 : Node := Node.split 3 T2185 T2188
theorem T2184_ok : Node.check D_R22222 T2184 [((163/256),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2185_ok T2188_ok
def T2183 : Node := Node.leaf L2183
theorem T2183_ok : Node.check D_R22222 T2183 [((0),(163/256)),((405/256),(1215/512)),((1215/512),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2183_ok
def T2182 : Node := Node.split 0 T2183 T2184
theorem T2182_ok : Node.check D_R22222 T2182 [((0),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2183_ok T2184_ok
def T2181 : Node := Node.leaf L2181
theorem T2181_ok : Node.check D_R22222 T2181 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2181_ok
def T2180 : Node := Node.leaf L2180
theorem T2180_ok : Node.check D_R22222 T2180 [((489/512),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L2180_ok
def T2179 : Node := Node.leaf L2179
theorem T2179_ok : Node.check D_R22222 T2179 [((489/512),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L2179_ok
def T2178 : Node := Node.split 3 T2179 T2180
theorem T2178_ok : Node.check D_R22222 T2178 [((489/512),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2179_ok T2180_ok
def T2177 : Node := Node.leaf L2177
theorem T2177_ok : Node.check D_R22222 T2177 [((163/256),(489/512)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2177_ok
def T2176 : Node := Node.split 0 T2177 T2178
theorem T2176_ok : Node.check D_R22222 T2176 [((163/256),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2177_ok T2178_ok
def T2175 : Node := Node.leaf L2175
theorem T2175_ok : Node.check D_R22222 T2175 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2175_ok
def T2174 : Node := Node.split 2 T2175 T2176
theorem T2174_ok : Node.check D_R22222 T2174 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2175_ok T2176_ok
def T2173 : Node := Node.leaf L2173
theorem T2173_ok : Node.check D_R22222 T2173 [((163/256),(163/128)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2173_ok
def T2172 : Node := Node.leaf L2172
theorem T2172_ok : Node.check D_R22222 T2172 [((163/256),(163/128)),((405/256),(2025/1024)),((405/256),(2025/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2172_ok
def T2171 : Node := Node.split 2 T2172 T2173
theorem T2171_ok : Node.check D_R22222 T2171 [((163/256),(163/128)),((405/256),(2025/1024)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2172_ok T2173_ok
def T2170 : Node := Node.split 1 T2171 T2174
theorem T2170_ok : Node.check D_R22222 T2170 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2171_ok T2174_ok
def T2169 : Node := Node.split 3 T2170 T2181
theorem T2169_ok : Node.check D_R22222 T2169 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2170_ok T2181_ok
def T2168 : Node := Node.leaf L2168
theorem T2168_ok : Node.check D_R22222 T2168 [((0),(163/256)),((405/256),(1215/512)),((405/256),(1215/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2168_ok
def T2167 : Node := Node.split 0 T2168 T2169
theorem T2167_ok : Node.check D_R22222 T2167 [((0),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2168_ok T2169_ok
def T2166 : Node := Node.split 2 T2167 T2182
theorem T2166_ok : Node.check D_R22222 T2166 [((0),(163/128)),((405/256),(1215/512)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2167_ok T2182_ok
def T2165 : Node := Node.split 1 T2166 T2189
theorem T2165_ok : Node.check D_R22222 T2165 [((0),(163/128)),((405/256),(405/128)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2166_ok T2189_ok
def T2164 : Node := Node.split 3 T2165 T2198
theorem T2164_ok : Node.check D_R22222 T2164 [((0),(163/128)),((405/256),(405/128)),((405/256),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2165_ok T2198_ok
def T2163 : Node := Node.split 0 T2164 T2209
theorem T2163_ok : Node.check D_R22222 T2163 [((0),(163/64)),((405/256),(405/128)),((405/256),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2164_ok T2209_ok
def T2162 : Node := Node.leaf L2162
theorem T2162_ok : Node.check D_R22222 T2162 [((163/128),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2162_ok
def T2161 : Node := Node.leaf L2161
theorem T2161_ok : Node.check D_R22222 T2161 [((163/128),(163/64)),((1215/512),(405/128)),((0),(405/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2161_ok
def T2160 : Node := Node.split 2 T2161 T2162
theorem T2160_ok : Node.check D_R22222 T2160 [((163/128),(163/64)),((1215/512),(405/128)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2161_ok T2162_ok
def T2159 : Node := Node.leaf L2159
theorem T2159_ok : Node.check D_R22222 T2159 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L2159_ok
def T2158 : Node := Node.leaf L2158
theorem T2158_ok : Node.check D_R22222 T2158 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/512),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L2158_ok
def T2157 : Node := Node.leaf L2157
theorem T2157_ok : Node.check D_R22222 T2157 [((489/256),(163/64)),((405/256),(2025/1024)),((405/512),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L2157_ok
def T2156 : Node := Node.split 1 T2157 T2158
theorem T2156_ok : Node.check D_R22222 T2156 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2157_ok T2158_ok
def T2155 : Node := Node.split 3 T2156 T2159
theorem T2155_ok : Node.check D_R22222 T2155 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2156_ok T2159_ok
def T2154 : Node := Node.leaf L2154
theorem T2154_ok : Node.check D_R22222 T2154 [((163/128),(489/256)),((405/256),(1215/512)),((405/512),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2154_ok
def T2153 : Node := Node.split 0 T2154 T2155
theorem T2153_ok : Node.check D_R22222 T2153 [((163/128),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2154_ok T2155_ok
def T2152 : Node := Node.leaf L2152
theorem T2152_ok : Node.check D_R22222 T2152 [((163/128),(163/64)),((405/256),(1215/512)),((0),(405/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2152_ok
def T2151 : Node := Node.split 2 T2152 T2153
theorem T2151_ok : Node.check D_R22222 T2151 [((163/128),(163/64)),((405/256),(1215/512)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2152_ok T2153_ok
def T2150 : Node := Node.split 1 T2151 T2160
theorem T2150_ok : Node.check D_R22222 T2150 [((163/128),(163/64)),((405/256),(405/128)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2151_ok T2160_ok
def T2149 : Node := Node.leaf L2149
theorem T2149_ok : Node.check D_R22222 T2149 [((489/256),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2149_ok
def T2148 : Node := Node.leaf L2148
theorem T2148_ok : Node.check D_R22222 T2148 [((489/256),(163/64)),((2835/1024),(405/128)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2148_ok
def T2147 : Node := Node.leaf L2147
theorem T2147_ok : Node.check D_R22222 T2147 [((489/256),(163/64)),((1215/512),(2835/1024)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2147_ok
def T2146 : Node := Node.split 1 T2147 T2148
theorem T2146_ok : Node.check D_R22222 T2146 [((489/256),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2147_ok T2148_ok
def T2145 : Node := Node.split 3 T2146 T2149
theorem T2145_ok : Node.check D_R22222 T2145 [((489/256),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2146_ok T2149_ok
def T2144 : Node := Node.leaf L2144
theorem T2144_ok : Node.check D_R22222 T2144 [((163/128),(489/256)),((1215/512),(405/128)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2144_ok
def T2143 : Node := Node.split 0 T2144 T2145
theorem T2143_ok : Node.check D_R22222 T2143 [((163/128),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2144_ok T2145_ok
def T2142 : Node := Node.leaf L2142
theorem T2142_ok : Node.check D_R22222 T2142 [((163/128),(163/64)),((1215/512),(405/128)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2142_ok
def T2141 : Node := Node.split 2 T2142 T2143
theorem T2141_ok : Node.check D_R22222 T2141 [((163/128),(163/64)),((1215/512),(405/128)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2142_ok T2143_ok
def T2140 : Node := Node.leaf L2140
theorem T2140_ok : Node.check D_R22222 T2140 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2140_ok
def T2139 : Node := Node.leaf L2139
theorem T2139_ok : Node.check D_R22222 T2139 [((489/256),(163/64)),((405/256),(2025/1024)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2139_ok
def T2138 : Node := Node.split 1 T2139 T2140
theorem T2138_ok : Node.check D_R22222 T2138 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2139_ok T2140_ok
def T2137 : Node := Node.leaf L2137
theorem T2137_ok : Node.check D_R22222 T2137 [((489/256),(163/64)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2137_ok
def T2136 : Node := Node.leaf L2136
theorem T2136_ok : Node.check D_R22222 T2136 [((1141/512),(163/64)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2136_ok
def T2135 : Node := Node.leaf L2135
theorem T2135_ok : Node.check D_R22222 T2135 [((489/256),(1141/512)),((4455/2048),(1215/512)),((405/512),(1215/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L2135_ok
def T2134 : Node := Node.leaf L2134
theorem T2134_ok : Node.check D_R22222 T2134 [((2119/1024),(1141/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L2134_ok
def T2133 : Node := Node.leaf L2133
theorem T2133_ok : Node.check D_R22222 T2133 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L2133_ok
def T2132 : Node := Node.leaf L2132
theorem T2132_ok : Node.check D_R22222 T2132 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L2132_ok
def T2131 : Node := Node.leaf L2131
theorem T2131_ok : Node.check D_R22222 T2131 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L2131_ok
def T2130 : Node := Node.split 2 T2131 T2132
theorem T2130_ok : Node.check D_R22222 T2130 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2131_ok T2132_ok
def T2129 : Node := Node.split 1 T2130 T2133
theorem T2129_ok : Node.check D_R22222 T2129 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2130_ok T2133_ok
def T2128 : Node := Node.leaf L2128
theorem T2128_ok : Node.check D_R22222 T2128 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L2128_ok
def T2127 : Node := Node.leaf L2127
theorem T2127_ok : Node.check D_R22222 T2127 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L2127_ok
def T2126 : Node := Node.split 1 T2127 T2128
theorem T2126_ok : Node.check D_R22222 T2126 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2127_ok T2128_ok
def T2125 : Node := Node.split 3 T2126 T2129
theorem T2125_ok : Node.check D_R22222 T2125 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2126_ok T2129_ok
def T2124 : Node := Node.split 0 T2125 T2134
theorem T2124_ok : Node.check D_R22222 T2124 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2125_ok T2134_ok
def T2123 : Node := Node.leaf L2123
theorem T2123_ok : Node.check D_R22222 T2123 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((405/512),(2025/2048)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L2123_ok
def T2122 : Node := Node.split 2 T2123 T2124
theorem T2122_ok : Node.check D_R22222 T2122 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2123_ok T2124_ok
def T2121 : Node := Node.split 1 T2122 T2135
theorem T2121_ok : Node.check D_R22222 T2121 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2122_ok T2135_ok
def T2120 : Node := Node.leaf L2120
theorem T2120_ok : Node.check D_R22222 T2120 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L2120_ok
def T2119 : Node := Node.split 3 T2120 T2121
theorem T2119_ok : Node.check D_R22222 T2119 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2120_ok T2121_ok
def T2118 : Node := Node.split 0 T2119 T2136
theorem T2118_ok : Node.check D_R22222 T2118 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2119_ok T2136_ok
def T2117 : Node := Node.split 2 T2118 T2137
theorem T2117_ok : Node.check D_R22222 T2117 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2118_ok T2137_ok
def T2116 : Node := Node.leaf L2116
theorem T2116_ok : Node.check D_R22222 T2116 [((489/256),(163/64)),((405/256),(2025/1024)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2116_ok
def T2115 : Node := Node.leaf L2115
theorem T2115_ok : Node.check D_R22222 T2115 [((489/256),(163/64)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2115_ok
def T2114 : Node := Node.split 2 T2115 T2116
theorem T2114_ok : Node.check D_R22222 T2114 [((489/256),(163/64)),((405/256),(2025/1024)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2115_ok T2116_ok
def T2113 : Node := Node.split 1 T2114 T2117
theorem T2113_ok : Node.check D_R22222 T2113 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2114_ok T2117_ok
def T2112 : Node := Node.split 3 T2113 T2138
theorem T2112_ok : Node.check D_R22222 T2112 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2113_ok T2138_ok
def T2111 : Node := Node.leaf L2111
theorem T2111_ok : Node.check D_R22222 T2111 [((163/128),(489/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2111_ok
def T2110 : Node := Node.split 0 T2111 T2112
theorem T2110_ok : Node.check D_R22222 T2110 [((163/128),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2111_ok T2112_ok
def T2109 : Node := Node.leaf L2109
theorem T2109_ok : Node.check D_R22222 T2109 [((163/128),(163/64)),((405/256),(1215/512)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2109_ok
def T2108 : Node := Node.split 2 T2109 T2110
theorem T2108_ok : Node.check D_R22222 T2108 [((163/128),(163/64)),((405/256),(1215/512)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2109_ok T2110_ok
def T2107 : Node := Node.split 1 T2108 T2141
theorem T2107_ok : Node.check D_R22222 T2107 [((163/128),(163/64)),((405/256),(405/128)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2108_ok T2141_ok
def T2106 : Node := Node.split 3 T2107 T2150
theorem T2106_ok : Node.check D_R22222 T2106 [((163/128),(163/64)),((405/256),(405/128)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2107_ok T2150_ok
def T2105 : Node := Node.leaf L2105
theorem T2105_ok : Node.check D_R22222 T2105 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L2105_ok
def T2104 : Node := Node.leaf L2104
theorem T2104_ok : Node.check D_R22222 T2104 [((163/256),(163/128)),((2835/1024),(405/128)),((405/512),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L2104_ok
def T2103 : Node := Node.leaf L2103
theorem T2103_ok : Node.check D_R22222 T2103 [((163/256),(163/128)),((1215/512),(2835/1024)),((405/512),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L2103_ok
def T2102 : Node := Node.split 1 T2103 T2104
theorem T2102_ok : Node.check D_R22222 T2102 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2103_ok T2104_ok
def T2101 : Node := Node.split 3 T2102 T2105
theorem T2101_ok : Node.check D_R22222 T2101 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2102_ok T2105_ok
def T2100 : Node := Node.leaf L2100
theorem T2100_ok : Node.check D_R22222 T2100 [((0),(163/256)),((1215/512),(405/128)),((405/512),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2100_ok
def T2099 : Node := Node.split 0 T2100 T2101
theorem T2099_ok : Node.check D_R22222 T2099 [((0),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2100_ok T2101_ok
def T2098 : Node := Node.leaf L2098
theorem T2098_ok : Node.check D_R22222 T2098 [((0),(163/128)),((1215/512),(405/128)),((0),(405/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2098_ok
def T2097 : Node := Node.split 2 T2098 T2099
theorem T2097_ok : Node.check D_R22222 T2097 [((0),(163/128)),((1215/512),(405/128)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2098_ok T2099_ok
def T2096 : Node := Node.leaf L2096
theorem T2096_ok : Node.check D_R22222 T2096 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L2096_ok
def T2095 : Node := Node.leaf L2095
theorem T2095_ok : Node.check D_R22222 T2095 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L2095_ok
def T2094 : Node := Node.split 2 T2095 T2096
theorem T2094_ok : Node.check D_R22222 T2094 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(405/256)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2095_ok T2096_ok
def T2093 : Node := Node.leaf L2093
theorem T2093_ok : Node.check D_R22222 T2093 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(405/256)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L2093_ok
def T2092 : Node := Node.split 1 T2093 T2094
theorem T2092_ok : Node.check D_R22222 T2092 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2093_ok T2094_ok
def T2091 : Node := Node.leaf L2091
theorem T2091_ok : Node.check D_R22222 T2091 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L2091_ok
def T2090 : Node := Node.leaf L2090
theorem T2090_ok : Node.check D_R22222 T2090 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((2119/512),(1141/256))] = true := Node.check_leaf_of _ _ _ L2090_ok
def T2089 : Node := Node.leaf L2089
theorem T2089_ok : Node.check D_R22222 T2089 [((489/512),(163/128)),((4455/2048),(1215/512)),((405/512),(1215/1024)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L2089_ok
def T2088 : Node := Node.leaf L2088
theorem T2088_ok : Node.check D_R22222 T2088 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L2088_ok
def T2087 : Node := Node.leaf L2087
theorem T2087_ok : Node.check D_R22222 T2087 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L2087_ok
def T2086 : Node := Node.leaf L2086
theorem T2086_ok : Node.check D_R22222 T2086 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L2086_ok
def T2085 : Node := Node.split 1 T2086 T2087
theorem T2085_ok : Node.check D_R22222 T2085 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2086_ok T2087_ok
def T2084 : Node := Node.leaf L2084
theorem T2084_ok : Node.check D_R22222 T2084 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L2084_ok
def T2083 : Node := Node.leaf L2083
theorem T2083_ok : Node.check D_R22222 T2083 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L2083_ok
def T2082 : Node := Node.split 1 T2083 T2084
theorem T2082_ok : Node.check D_R22222 T2082 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2083_ok T2084_ok
def T2081 : Node := Node.split 3 T2082 T2085
theorem T2081_ok : Node.check D_R22222 T2081 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2082_ok T2085_ok
def T2080 : Node := Node.split 0 T2081 T2088
theorem T2080_ok : Node.check D_R22222 T2080 [((489/512),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2081_ok T2088_ok
def T2079 : Node := Node.leaf L2079
theorem T2079_ok : Node.check D_R22222 T2079 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/512),(2025/2048)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L2079_ok
def T2078 : Node := Node.split 2 T2079 T2080
theorem T2078_ok : Node.check D_R22222 T2078 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/512),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2079_ok T2080_ok
def T2077 : Node := Node.split 1 T2078 T2089
theorem T2077_ok : Node.check D_R22222 T2077 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2078_ok T2089_ok
def T2076 : Node := Node.split 3 T2077 T2090
theorem T2076_ok : Node.check D_R22222 T2076 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2077_ok T2090_ok
def T2075 : Node := Node.leaf L2075
theorem T2075_ok : Node.check D_R22222 T2075 [((163/256),(489/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L2075_ok
def T2074 : Node := Node.split 0 T2075 T2076
theorem T2074_ok : Node.check D_R22222 T2074 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2075_ok T2076_ok
def T2073 : Node := Node.split 2 T2074 T2091
theorem T2073_ok : Node.check D_R22222 T2073 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2074_ok T2091_ok
def T2072 : Node := Node.leaf L2072
theorem T2072_ok : Node.check D_R22222 T2072 [((163/256),(163/128)),((405/256),(2025/1024)),((1215/1024),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L2072_ok
def T2071 : Node := Node.leaf L2071
theorem T2071_ok : Node.check D_R22222 T2071 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L2071_ok
def T2070 : Node := Node.split 2 T2071 T2072
theorem T2070_ok : Node.check D_R22222 T2070 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2071_ok T2072_ok
def T2069 : Node := Node.split 1 T2070 T2073
theorem T2069_ok : Node.check D_R22222 T2069 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2070_ok T2073_ok
def T2068 : Node := Node.split 3 T2069 T2092
theorem T2068_ok : Node.check D_R22222 T2068 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2069_ok T2092_ok
def T2067 : Node := Node.leaf L2067
theorem T2067_ok : Node.check D_R22222 T2067 [((0),(163/256)),((405/256),(1215/512)),((405/512),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2067_ok
def T2066 : Node := Node.split 0 T2067 T2068
theorem T2066_ok : Node.check D_R22222 T2066 [((0),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2067_ok T2068_ok
def T2065 : Node := Node.leaf L2065
theorem T2065_ok : Node.check D_R22222 T2065 [((0),(163/128)),((405/256),(1215/512)),((0),(405/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L2065_ok
def T2064 : Node := Node.split 2 T2065 T2066
theorem T2064_ok : Node.check D_R22222 T2064 [((0),(163/128)),((405/256),(1215/512)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2065_ok T2066_ok
def T2063 : Node := Node.split 1 T2064 T2097
theorem T2063_ok : Node.check D_R22222 T2063 [((0),(163/128)),((405/256),(405/128)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2064_ok T2097_ok
def T2062 : Node := Node.leaf L2062
theorem T2062_ok : Node.check D_R22222 T2062 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2062_ok
def T2061 : Node := Node.leaf L2061
theorem T2061_ok : Node.check D_R22222 T2061 [((163/256),(163/128)),((2835/1024),(405/128)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2061_ok
def T2060 : Node := Node.leaf L2060
theorem T2060_ok : Node.check D_R22222 T2060 [((163/256),(163/128)),((2835/1024),(405/128)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2060_ok
def T2059 : Node := Node.split 2 T2060 T2061
theorem T2059_ok : Node.check D_R22222 T2059 [((163/256),(163/128)),((2835/1024),(405/128)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2060_ok T2061_ok
def T2058 : Node := Node.leaf L2058
theorem T2058_ok : Node.check D_R22222 T2058 [((163/256),(163/128)),((1215/512),(2835/1024)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2058_ok
def T2057 : Node := Node.split 1 T2058 T2059
theorem T2057_ok : Node.check D_R22222 T2057 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2058_ok T2059_ok
def T2056 : Node := Node.split 3 T2057 T2062
theorem T2056_ok : Node.check D_R22222 T2056 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2057_ok T2062_ok
def T2055 : Node := Node.leaf L2055
theorem T2055_ok : Node.check D_R22222 T2055 [((0),(163/256)),((1215/512),(405/128)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2055_ok
def T2054 : Node := Node.split 0 T2055 T2056
theorem T2054_ok : Node.check D_R22222 T2054 [((0),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2055_ok T2056_ok
def T2053 : Node := Node.leaf L2053
theorem T2053_ok : Node.check D_R22222 T2053 [((0),(163/128)),((1215/512),(405/128)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L2053_ok
def T2052 : Node := Node.split 2 T2053 T2054
theorem T2052_ok : Node.check D_R22222 T2052 [((0),(163/128)),((1215/512),(405/128)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2053_ok T2054_ok
def T2051 : Node := Node.leaf L2051
theorem T2051_ok : Node.check D_R22222 T2051 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2051_ok
def T2050 : Node := Node.leaf L2050
theorem T2050_ok : Node.check D_R22222 T2050 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2050_ok
def T2049 : Node := Node.split 2 T2050 T2051
theorem T2049_ok : Node.check D_R22222 T2049 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(405/256)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2050_ok T2051_ok
def T2048 : Node := Node.leaf L2048
theorem T2048_ok : Node.check D_R22222 T2048 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L2048_ok
def T2047 : Node := Node.split 1 T2048 T2049
theorem T2047_ok : Node.check D_R22222 T2047 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2048_ok T2049_ok
def T2046 : Node := Node.leaf L2046
theorem T2046_ok : Node.check D_R22222 T2046 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2046_ok
def T2045 : Node := Node.leaf L2045
theorem T2045_ok : Node.check D_R22222 T2045 [((489/512),(163/128)),((4455/2048),(1215/512)),((405/512),(1215/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L2045_ok
def T2044 : Node := Node.leaf L2044
theorem T2044_ok : Node.check D_R22222 T2044 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L2044_ok
def T2043 : Node := Node.leaf L2043
theorem T2043_ok : Node.check D_R22222 T2043 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L2043_ok
def T2042 : Node := Node.leaf L2042
theorem T2042_ok : Node.check D_R22222 T2042 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L2042_ok
def T2041 : Node := Node.leaf L2041
theorem T2041_ok : Node.check D_R22222 T2041 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L2041_ok
def T2040 : Node := Node.leaf L2040
theorem T2040_ok : Node.check D_R22222 T2040 [((489/512),(2119/2048)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L2040_ok
def T2039 : Node := Node.split 0 T2040 T2041
theorem T2039_ok : Node.check D_R22222 T2039 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2040_ok T2041_ok
def T2038 : Node := Node.split 2 T2039 T2042
theorem T2038_ok : Node.check D_R22222 T2038 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2039_ok T2042_ok
def T2037 : Node := Node.split 1 T2038 T2043
theorem T2037_ok : Node.check D_R22222 T2037 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2038_ok T2043_ok
def T2036 : Node := Node.leaf L2036
theorem T2036_ok : Node.check D_R22222 T2036 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L2036_ok
def T2035 : Node := Node.leaf L2035
theorem T2035_ok : Node.check D_R22222 T2035 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L2035_ok
def T2034 : Node := Node.split 2 T2035 T2036
theorem T2034_ok : Node.check D_R22222 T2034 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2035_ok T2036_ok
def T2033 : Node := Node.leaf L2033
theorem T2033_ok : Node.check D_R22222 T2033 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L2033_ok
def T2032 : Node := Node.leaf L2032
theorem T2032_ok : Node.check D_R22222 T2032 [((489/512),(2119/2048)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L2032_ok
def T2031 : Node := Node.split 0 T2032 T2033
theorem T2031_ok : Node.check D_R22222 T2031 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2032_ok T2033_ok
def T2030 : Node := Node.leaf L2030
theorem T2030_ok : Node.check D_R22222 T2030 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L2030_ok
def T2029 : Node := Node.split 2 T2030 T2031
theorem T2029_ok : Node.check D_R22222 T2029 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2030_ok T2031_ok
def T2028 : Node := Node.split 1 T2029 T2034
theorem T2028_ok : Node.check D_R22222 T2028 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2029_ok T2034_ok
def T2027 : Node := Node.split 3 T2028 T2037
theorem T2027_ok : Node.check D_R22222 T2027 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2028_ok T2037_ok
def T2026 : Node := Node.split 0 T2027 T2044
theorem T2026_ok : Node.check D_R22222 T2026 [((489/512),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2027_ok T2044_ok
def T2025 : Node := Node.leaf L2025
theorem T2025_ok : Node.check D_R22222 T2025 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/512),(2025/2048)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L2025_ok
def T2024 : Node := Node.split 2 T2025 T2026
theorem T2024_ok : Node.check D_R22222 T2024 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2025_ok T2026_ok
def T2023 : Node := Node.split 1 T2024 T2045
theorem T2023_ok : Node.check D_R22222 T2023 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2024_ok T2045_ok
def T2022 : Node := Node.leaf L2022
theorem T2022_ok : Node.check D_R22222 T2022 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L2022_ok
def T2021 : Node := Node.split 3 T2022 T2023
theorem T2021_ok : Node.check D_R22222 T2021 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2022_ok T2023_ok
def T2020 : Node := Node.leaf L2020
theorem T2020_ok : Node.check D_R22222 T2020 [((163/256),(489/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2020_ok
def T2019 : Node := Node.split 0 T2020 T2021
theorem T2019_ok : Node.check D_R22222 T2019 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2020_ok T2021_ok
def T2018 : Node := Node.split 2 T2019 T2046
theorem T2018_ok : Node.check D_R22222 T2018 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2019_ok T2046_ok
def T2017 : Node := Node.leaf L2017
theorem T2017_ok : Node.check D_R22222 T2017 [((163/256),(163/128)),((405/256),(2025/1024)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L2017_ok
def T2016 : Node := Node.leaf L2016
theorem T2016_ok : Node.check D_R22222 T2016 [((1141/1024),(163/128)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L2016_ok
def T2015 : Node := Node.leaf L2015
theorem T2015_ok : Node.check D_R22222 T2015 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L2015_ok
def T2014 : Node := Node.leaf L2014
theorem T2014_ok : Node.check D_R22222 T2014 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L2014_ok
def T2013 : Node := Node.split 2 T2014 T2015
theorem T2013_ok : Node.check D_R22222 T2013 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2014_ok T2015_ok
def T2012 : Node := Node.leaf L2012
theorem T2012_ok : Node.check D_R22222 T2012 [((489/512),(1141/1024)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L2012_ok
def T2011 : Node := Node.split 1 T2012 T2013
theorem T2011_ok : Node.check D_R22222 T2011 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2012_ok T2013_ok
def T2010 : Node := Node.leaf L2010
theorem T2010_ok : Node.check D_R22222 T2010 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L2010_ok
def T2009 : Node := Node.leaf L2009
theorem T2009_ok : Node.check D_R22222 T2009 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L2009_ok
def T2008 : Node := Node.split 2 T2009 T2010
theorem T2008_ok : Node.check D_R22222 T2008 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2009_ok T2010_ok
def T2007 : Node := Node.leaf L2007
theorem T2007_ok : Node.check D_R22222 T2007 [((489/512),(1141/1024)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L2007_ok
def T2006 : Node := Node.split 1 T2007 T2008
theorem T2006_ok : Node.check D_R22222 T2006 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2007_ok T2008_ok
def T2005 : Node := Node.split 3 T2006 T2011
theorem T2005_ok : Node.check D_R22222 T2005 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2006_ok T2011_ok
def T2004 : Node := Node.split 0 T2005 T2016
theorem T2004_ok : Node.check D_R22222 T2004 [((489/512),(163/128)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2005_ok T2016_ok
def T2003 : Node := Node.leaf L2003
theorem T2003_ok : Node.check D_R22222 T2003 [((489/512),(163/128)),((3645/2048),(2025/1024)),((405/512),(2025/2048)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L2003_ok
def T2002 : Node := Node.split 2 T2003 T2004
theorem T2002_ok : Node.check D_R22222 T2002 [((489/512),(163/128)),((3645/2048),(2025/1024)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2003_ok T2004_ok
def T2001 : Node := Node.leaf L2001
theorem T2001_ok : Node.check D_R22222 T2001 [((489/512),(163/128)),((405/256),(3645/2048)),((405/512),(1215/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L2001_ok
def T2000 : Node := Node.split 1 T2001 T2002
theorem T2000_ok : Node.check D_R22222 T2000 [((489/512),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2001_ok T2002_ok
def T1999 : Node := Node.leaf L1999
theorem T1999_ok : Node.check D_R22222 T1999 [((489/512),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L1999_ok
def T1998 : Node := Node.split 3 T1999 T2000
theorem T1998_ok : Node.check D_R22222 T1998 [((489/512),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1999_ok T2000_ok
def T1997 : Node := Node.leaf L1997
theorem T1997_ok : Node.check D_R22222 T1997 [((163/256),(489/512)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1997_ok
def T1996 : Node := Node.split 0 T1997 T1998
theorem T1996_ok : Node.check D_R22222 T1996 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1997_ok T1998_ok
def T1995 : Node := Node.split 2 T1996 T2017
theorem T1995_ok : Node.check D_R22222 T1995 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1996_ok T2017_ok
def T1994 : Node := Node.split 1 T1995 T2018
theorem T1994_ok : Node.check D_R22222 T1994 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1995_ok T2018_ok
def T1993 : Node := Node.split 3 T1994 T2047
theorem T1993_ok : Node.check D_R22222 T1993 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1994_ok T2047_ok
def T1992 : Node := Node.leaf L1992
theorem T1992_ok : Node.check D_R22222 T1992 [((0),(163/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1992_ok
def T1991 : Node := Node.split 0 T1992 T1993
theorem T1991_ok : Node.check D_R22222 T1991 [((0),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1992_ok T1993_ok
def T1990 : Node := Node.leaf L1990
theorem T1990_ok : Node.check D_R22222 T1990 [((0),(163/128)),((405/256),(1215/512)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1990_ok
def T1989 : Node := Node.split 2 T1990 T1991
theorem T1989_ok : Node.check D_R22222 T1989 [((0),(163/128)),((405/256),(1215/512)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1990_ok T1991_ok
def T1988 : Node := Node.split 1 T1989 T2052
theorem T1988_ok : Node.check D_R22222 T1988 [((0),(163/128)),((405/256),(405/128)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1989_ok T2052_ok
def T1987 : Node := Node.split 3 T1988 T2063
theorem T1987_ok : Node.check D_R22222 T1987 [((0),(163/128)),((405/256),(405/128)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1988_ok T2063_ok
def T1986 : Node := Node.split 0 T1987 T2106
theorem T1986_ok : Node.check D_R22222 T1986 [((0),(163/64)),((405/256),(405/128)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1987_ok T2106_ok
def T1985 : Node := Node.split 2 T1986 T2163
theorem T1985_ok : Node.check D_R22222 T1985 [((0),(163/64)),((405/256),(405/128)),((0),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1986_ok T2163_ok
def T1984 : Node := Node.leaf L1984
theorem T1984_ok : Node.check D_R22222 T1984 [((163/128),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1984_ok
def T1983 : Node := Node.leaf L1983
theorem T1983_ok : Node.check D_R22222 T1983 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1983_ok
def T1982 : Node := Node.leaf L1982
theorem T1982_ok : Node.check D_R22222 T1982 [((489/256),(163/64)),((1215/1024),(405/256)),((405/256),(1215/512)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1982_ok
def T1981 : Node := Node.leaf L1981
theorem T1981_ok : Node.check D_R22222 T1981 [((489/256),(163/64)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1981_ok
def T1980 : Node := Node.leaf L1980
theorem T1980_ok : Node.check D_R22222 T1980 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1980_ok
def T1979 : Node := Node.split 2 T1980 T1981
theorem T1979_ok : Node.check D_R22222 T1979 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(1215/512)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1980_ok T1981_ok
def T1978 : Node := Node.split 1 T1979 T1982
theorem T1978_ok : Node.check D_R22222 T1978 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1979_ok T1982_ok
def T1977 : Node := Node.split 3 T1978 T1983
theorem T1977_ok : Node.check D_R22222 T1977 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1978_ok T1983_ok
def T1976 : Node := Node.leaf L1976
theorem T1976_ok : Node.check D_R22222 T1976 [((163/128),(489/256)),((405/512),(405/256)),((405/256),(1215/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1976_ok
def T1975 : Node := Node.split 0 T1976 T1977
theorem T1975_ok : Node.check D_R22222 T1975 [((163/128),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1976_ok T1977_ok
def T1974 : Node := Node.split 2 T1975 T1984
theorem T1974_ok : Node.check D_R22222 T1974 [((163/128),(163/64)),((405/512),(405/256)),((405/256),(405/128)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1975_ok T1984_ok
def T1973 : Node := Node.leaf L1973
theorem T1973_ok : Node.check D_R22222 T1973 [((163/128),(163/64)),((0),(405/512)),((405/256),(405/128)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1973_ok
def T1972 : Node := Node.split 1 T1973 T1974
theorem T1972_ok : Node.check D_R22222 T1972 [((163/128),(163/64)),((0),(405/256)),((405/256),(405/128)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1973_ok T1974_ok
def T1971 : Node := Node.leaf L1971
theorem T1971_ok : Node.check D_R22222 T1971 [((489/256),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1971_ok
def T1970 : Node := Node.leaf L1970
theorem T1970_ok : Node.check D_R22222 T1970 [((489/256),(163/64)),((1215/1024),(405/256)),((1215/512),(405/128)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1970_ok
def T1969 : Node := Node.leaf L1969
theorem T1969_ok : Node.check D_R22222 T1969 [((489/256),(163/64)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1969_ok
def T1968 : Node := Node.leaf L1968
theorem T1968_ok : Node.check D_R22222 T1968 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/512),(2835/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1968_ok
def T1967 : Node := Node.split 2 T1968 T1969
theorem T1967_ok : Node.check D_R22222 T1967 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/512),(405/128)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1968_ok T1969_ok
def T1966 : Node := Node.split 1 T1967 T1970
theorem T1966_ok : Node.check D_R22222 T1966 [((489/256),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1967_ok T1970_ok
def T1965 : Node := Node.split 3 T1966 T1971
theorem T1965_ok : Node.check D_R22222 T1965 [((489/256),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1966_ok T1971_ok
def T1964 : Node := Node.leaf L1964
theorem T1964_ok : Node.check D_R22222 T1964 [((163/128),(489/256)),((405/512),(405/256)),((1215/512),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1964_ok
def T1963 : Node := Node.split 0 T1964 T1965
theorem T1963_ok : Node.check D_R22222 T1963 [((163/128),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1964_ok T1965_ok
def T1962 : Node := Node.leaf L1962
theorem T1962_ok : Node.check D_R22222 T1962 [((489/256),(163/64)),((1215/1024),(405/256)),((405/256),(1215/512)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1962_ok
def T1961 : Node := Node.leaf L1961
theorem T1961_ok : Node.check D_R22222 T1961 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(1215/512)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1961_ok
def T1960 : Node := Node.split 1 T1961 T1962
theorem T1960_ok : Node.check D_R22222 T1960 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1961_ok T1962_ok
def T1959 : Node := Node.leaf L1959
theorem T1959_ok : Node.check D_R22222 T1959 [((489/256),(163/64)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1959_ok
def T1958 : Node := Node.leaf L1958
theorem T1958_ok : Node.check D_R22222 T1958 [((1141/512),(163/64)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1958_ok
def T1957 : Node := Node.leaf L1957
theorem T1957_ok : Node.check D_R22222 T1957 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((4455/2048),(1215/512)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1957_ok
def T1956 : Node := Node.leaf L1956
theorem T1956_ok : Node.check D_R22222 T1956 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1956_ok
def T1955 : Node := Node.leaf L1955
theorem T1955_ok : Node.check D_R22222 T1955 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1955_ok
def T1954 : Node := Node.leaf L1954
theorem T1954_ok : Node.check D_R22222 T1954 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1954_ok
def T1953 : Node := Node.split 1 T1954 T1955
theorem T1953_ok : Node.check D_R22222 T1953 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1954_ok T1955_ok
def T1952 : Node := Node.leaf L1952
theorem T1952_ok : Node.check D_R22222 T1952 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1952_ok
def T1951 : Node := Node.leaf L1951
theorem T1951_ok : Node.check D_R22222 T1951 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1951_ok
def T1950 : Node := Node.split 1 T1951 T1952
theorem T1950_ok : Node.check D_R22222 T1950 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1951_ok T1952_ok
def T1949 : Node := Node.split 3 T1950 T1953
theorem T1949_ok : Node.check D_R22222 T1949 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1950_ok T1953_ok
def T1948 : Node := Node.split 0 T1949 T1956
theorem T1948_ok : Node.check D_R22222 T1948 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1949_ok T1956_ok
def T1947 : Node := Node.split 2 T1948 T1957
theorem T1947_ok : Node.check D_R22222 T1947 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(1215/512)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1948_ok T1957_ok
def T1946 : Node := Node.leaf L1946
theorem T1946_ok : Node.check D_R22222 T1946 [((489/256),(1141/512)),((405/512),(2025/2048)),((2025/1024),(1215/512)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1946_ok
def T1945 : Node := Node.split 1 T1946 T1947
theorem T1945_ok : Node.check D_R22222 T1945 [((489/256),(1141/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1946_ok T1947_ok
def T1944 : Node := Node.leaf L1944
theorem T1944_ok : Node.check D_R22222 T1944 [((489/256),(1141/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L1944_ok
def T1943 : Node := Node.split 3 T1944 T1945
theorem T1943_ok : Node.check D_R22222 T1943 [((489/256),(1141/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1944_ok T1945_ok
def T1942 : Node := Node.split 0 T1943 T1958
theorem T1942_ok : Node.check D_R22222 T1942 [((489/256),(163/64)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1943_ok T1958_ok
def T1941 : Node := Node.leaf L1941
theorem T1941_ok : Node.check D_R22222 T1941 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1941_ok
def T1940 : Node := Node.split 2 T1941 T1942
theorem T1940_ok : Node.check D_R22222 T1940 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1941_ok T1942_ok
def T1939 : Node := Node.split 1 T1940 T1959
theorem T1939_ok : Node.check D_R22222 T1939 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1940_ok T1959_ok
def T1938 : Node := Node.split 3 T1939 T1960
theorem T1938_ok : Node.check D_R22222 T1938 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1939_ok T1960_ok
def T1937 : Node := Node.leaf L1937
theorem T1937_ok : Node.check D_R22222 T1937 [((163/128),(489/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1937_ok
def T1936 : Node := Node.split 0 T1937 T1938
theorem T1936_ok : Node.check D_R22222 T1936 [((163/128),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1937_ok T1938_ok
def T1935 : Node := Node.split 2 T1936 T1963
theorem T1935_ok : Node.check D_R22222 T1935 [((163/128),(163/64)),((405/512),(405/256)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1936_ok T1963_ok
def T1934 : Node := Node.leaf L1934
theorem T1934_ok : Node.check D_R22222 T1934 [((163/128),(163/64)),((0),(405/512)),((405/256),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1934_ok
def T1933 : Node := Node.split 1 T1934 T1935
theorem T1933_ok : Node.check D_R22222 T1933 [((163/128),(163/64)),((0),(405/256)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1934_ok T1935_ok
def T1932 : Node := Node.split 3 T1933 T1972
theorem T1932_ok : Node.check D_R22222 T1932 [((163/128),(163/64)),((0),(405/256)),((405/256),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1933_ok T1972_ok
def T1931 : Node := Node.leaf L1931
theorem T1931_ok : Node.check D_R22222 T1931 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1931_ok
def T1930 : Node := Node.leaf L1930
theorem T1930_ok : Node.check D_R22222 T1930 [((163/256),(163/128)),((1215/1024),(405/256)),((1215/512),(405/128)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1930_ok
def T1929 : Node := Node.leaf L1929
theorem T1929_ok : Node.check D_R22222 T1929 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/512),(405/128)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1929_ok
def T1928 : Node := Node.split 1 T1929 T1930
theorem T1928_ok : Node.check D_R22222 T1928 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1929_ok T1930_ok
def T1927 : Node := Node.split 3 T1928 T1931
theorem T1927_ok : Node.check D_R22222 T1927 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1928_ok T1931_ok
def T1926 : Node := Node.leaf L1926
theorem T1926_ok : Node.check D_R22222 T1926 [((0),(163/256)),((405/512),(405/256)),((1215/512),(405/128)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1926_ok
def T1925 : Node := Node.split 0 T1926 T1927
theorem T1925_ok : Node.check D_R22222 T1925 [((0),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1926_ok T1927_ok
def T1924 : Node := Node.leaf L1924
theorem T1924_ok : Node.check D_R22222 T1924 [((163/256),(163/128)),((1215/1024),(405/256)),((405/256),(1215/512)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1924_ok
def T1923 : Node := Node.leaf L1923
theorem T1923_ok : Node.check D_R22222 T1923 [((163/256),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1923_ok
def T1922 : Node := Node.leaf L1922
theorem T1922_ok : Node.check D_R22222 T1922 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1922_ok
def T1921 : Node := Node.split 2 T1922 T1923
theorem T1921_ok : Node.check D_R22222 T1921 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(1215/512)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1922_ok T1923_ok
def T1920 : Node := Node.split 1 T1921 T1924
theorem T1920_ok : Node.check D_R22222 T1920 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1921_ok T1924_ok
def T1919 : Node := Node.leaf L1919
theorem T1919_ok : Node.check D_R22222 T1919 [((163/256),(163/128)),((1215/1024),(405/256)),((405/256),(1215/512)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1919_ok
def T1918 : Node := Node.leaf L1918
theorem T1918_ok : Node.check D_R22222 T1918 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((2119/512),(1141/256))] = true := Node.check_leaf_of _ _ _ L1918_ok
def T1917 : Node := Node.leaf L1917
theorem T1917_ok : Node.check D_R22222 T1917 [((489/512),(163/128)),((2025/2048),(1215/1024)),((4455/2048),(1215/512)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L1917_ok
def T1916 : Node := Node.leaf L1916
theorem T1916_ok : Node.check D_R22222 T1916 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L1916_ok
def T1915 : Node := Node.leaf L1915
theorem T1915_ok : Node.check D_R22222 T1915 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1915_ok
def T1914 : Node := Node.leaf L1914
theorem T1914_ok : Node.check D_R22222 T1914 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1914_ok
def T1913 : Node := Node.split 1 T1914 T1915
theorem T1913_ok : Node.check D_R22222 T1913 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((4075/1024),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1914_ok T1915_ok
def T1912 : Node := Node.leaf L1912
theorem T1912_ok : Node.check D_R22222 T1912 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1912_ok
def T1911 : Node := Node.leaf L1911
theorem T1911_ok : Node.check D_R22222 T1911 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1911_ok
def T1910 : Node := Node.split 1 T1911 T1912
theorem T1910_ok : Node.check D_R22222 T1910 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/128),(4075/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1911_ok T1912_ok
def T1909 : Node := Node.split 3 T1910 T1913
theorem T1909_ok : Node.check D_R22222 T1909 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1910_ok T1913_ok
def T1908 : Node := Node.split 0 T1909 T1916
theorem T1908_ok : Node.check D_R22222 T1908 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1909_ok T1916_ok
def T1907 : Node := Node.split 2 T1908 T1917
theorem T1907_ok : Node.check D_R22222 T1907 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(1215/512)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1908_ok T1917_ok
def T1906 : Node := Node.leaf L1906
theorem T1906_ok : Node.check D_R22222 T1906 [((489/512),(163/128)),((405/512),(2025/2048)),((2025/1024),(1215/512)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L1906_ok
def T1905 : Node := Node.split 1 T1906 T1907
theorem T1905_ok : Node.check D_R22222 T1905 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1906_ok T1907_ok
def T1904 : Node := Node.split 3 T1905 T1918
theorem T1904_ok : Node.check D_R22222 T1904 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1905_ok T1918_ok
def T1903 : Node := Node.leaf L1903
theorem T1903_ok : Node.check D_R22222 T1903 [((163/256),(489/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1903_ok
def T1902 : Node := Node.split 0 T1903 T1904
theorem T1902_ok : Node.check D_R22222 T1902 [((163/256),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1903_ok T1904_ok
def T1901 : Node := Node.leaf L1901
theorem T1901_ok : Node.check D_R22222 T1901 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1901_ok
def T1900 : Node := Node.split 2 T1901 T1902
theorem T1900_ok : Node.check D_R22222 T1900 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(1215/512)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1901_ok T1902_ok
def T1899 : Node := Node.split 1 T1900 T1919
theorem T1899_ok : Node.check D_R22222 T1899 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1900_ok T1919_ok
def T1898 : Node := Node.split 3 T1899 T1920
theorem T1898_ok : Node.check D_R22222 T1898 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1899_ok T1920_ok
def T1897 : Node := Node.leaf L1897
theorem T1897_ok : Node.check D_R22222 T1897 [((0),(163/256)),((405/512),(405/256)),((405/256),(1215/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1897_ok
def T1896 : Node := Node.split 0 T1897 T1898
theorem T1896_ok : Node.check D_R22222 T1896 [((0),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1897_ok T1898_ok
def T1895 : Node := Node.split 2 T1896 T1925
theorem T1895_ok : Node.check D_R22222 T1895 [((0),(163/128)),((405/512),(405/256)),((405/256),(405/128)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1896_ok T1925_ok
def T1894 : Node := Node.leaf L1894
theorem T1894_ok : Node.check D_R22222 T1894 [((0),(163/128)),((0),(405/512)),((405/256),(405/128)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1894_ok
def T1893 : Node := Node.split 1 T1894 T1895
theorem T1893_ok : Node.check D_R22222 T1893 [((0),(163/128)),((0),(405/256)),((405/256),(405/128)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1894_ok T1895_ok
def T1892 : Node := Node.leaf L1892
theorem T1892_ok : Node.check D_R22222 T1892 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1892_ok
def T1891 : Node := Node.leaf L1891
theorem T1891_ok : Node.check D_R22222 T1891 [((163/256),(163/128)),((1215/1024),(405/256)),((1215/512),(405/128)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1891_ok
def T1890 : Node := Node.leaf L1890
theorem T1890_ok : Node.check D_R22222 T1890 [((163/256),(163/128)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1890_ok
def T1889 : Node := Node.leaf L1889
theorem T1889_ok : Node.check D_R22222 T1889 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/512),(2835/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1889_ok
def T1888 : Node := Node.split 2 T1889 T1890
theorem T1888_ok : Node.check D_R22222 T1888 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/512),(405/128)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1889_ok T1890_ok
def T1887 : Node := Node.split 1 T1888 T1891
theorem T1887_ok : Node.check D_R22222 T1887 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1888_ok T1891_ok
def T1886 : Node := Node.split 3 T1887 T1892
theorem T1886_ok : Node.check D_R22222 T1886 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1887_ok T1892_ok
def T1885 : Node := Node.leaf L1885
theorem T1885_ok : Node.check D_R22222 T1885 [((0),(163/256)),((405/512),(405/256)),((1215/512),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1885_ok
def T1884 : Node := Node.split 0 T1885 T1886
theorem T1884_ok : Node.check D_R22222 T1884 [((0),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1885_ok T1886_ok
def T1883 : Node := Node.leaf L1883
theorem T1883_ok : Node.check D_R22222 T1883 [((163/256),(163/128)),((1215/1024),(405/256)),((405/256),(1215/512)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1883_ok
def T1882 : Node := Node.leaf L1882
theorem T1882_ok : Node.check D_R22222 T1882 [((163/256),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1882_ok
def T1881 : Node := Node.leaf L1881
theorem T1881_ok : Node.check D_R22222 T1881 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1881_ok
def T1880 : Node := Node.split 2 T1881 T1882
theorem T1880_ok : Node.check D_R22222 T1880 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(1215/512)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1881_ok T1882_ok
def T1879 : Node := Node.split 1 T1880 T1883
theorem T1879_ok : Node.check D_R22222 T1879 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1880_ok T1883_ok
def T1878 : Node := Node.leaf L1878
theorem T1878_ok : Node.check D_R22222 T1878 [((163/256),(163/128)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1878_ok
def T1877 : Node := Node.leaf L1877
theorem T1877_ok : Node.check D_R22222 T1877 [((489/512),(163/128)),((2025/2048),(1215/1024)),((4455/2048),(1215/512)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1877_ok
def T1876 : Node := Node.leaf L1876
theorem T1876_ok : Node.check D_R22222 T1876 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1876_ok
def T1875 : Node := Node.leaf L1875
theorem T1875_ok : Node.check D_R22222 T1875 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1875_ok
def T1874 : Node := Node.leaf L1874
theorem T1874_ok : Node.check D_R22222 T1874 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1874_ok
def T1873 : Node := Node.split 1 T1874 T1875
theorem T1873_ok : Node.check D_R22222 T1873 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1874_ok T1875_ok
def T1872 : Node := Node.leaf L1872
theorem T1872_ok : Node.check D_R22222 T1872 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1872_ok
def T1871 : Node := Node.leaf L1871
theorem T1871_ok : Node.check D_R22222 T1871 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1871_ok
def T1870 : Node := Node.split 1 T1871 T1872
theorem T1870_ok : Node.check D_R22222 T1870 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1871_ok T1872_ok
def T1869 : Node := Node.split 3 T1870 T1873
theorem T1869_ok : Node.check D_R22222 T1869 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1870_ok T1873_ok
def T1868 : Node := Node.split 0 T1869 T1876
theorem T1868_ok : Node.check D_R22222 T1868 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1869_ok T1876_ok
def T1867 : Node := Node.split 2 T1868 T1877
theorem T1867_ok : Node.check D_R22222 T1867 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(1215/512)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1868_ok T1877_ok
def T1866 : Node := Node.leaf L1866
theorem T1866_ok : Node.check D_R22222 T1866 [((489/512),(163/128)),((405/512),(2025/2048)),((2025/1024),(1215/512)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1866_ok
def T1865 : Node := Node.split 1 T1866 T1867
theorem T1865_ok : Node.check D_R22222 T1865 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1866_ok T1867_ok
def T1864 : Node := Node.leaf L1864
theorem T1864_ok : Node.check D_R22222 T1864 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L1864_ok
def T1863 : Node := Node.split 3 T1864 T1865
theorem T1863_ok : Node.check D_R22222 T1863 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1864_ok T1865_ok
def T1862 : Node := Node.leaf L1862
theorem T1862_ok : Node.check D_R22222 T1862 [((163/256),(489/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1862_ok
def T1861 : Node := Node.split 0 T1862 T1863
theorem T1861_ok : Node.check D_R22222 T1861 [((163/256),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1862_ok T1863_ok
def T1860 : Node := Node.leaf L1860
theorem T1860_ok : Node.check D_R22222 T1860 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1860_ok
def T1859 : Node := Node.leaf L1859
theorem T1859_ok : Node.check D_R22222 T1859 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1859_ok
def T1858 : Node := Node.leaf L1858
theorem T1858_ok : Node.check D_R22222 T1858 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1858_ok
def T1857 : Node := Node.split 1 T1858 T1859
theorem T1857_ok : Node.check D_R22222 T1857 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1858_ok T1859_ok
def T1856 : Node := Node.leaf L1856
theorem T1856_ok : Node.check D_R22222 T1856 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1856_ok
def T1855 : Node := Node.leaf L1855
theorem T1855_ok : Node.check D_R22222 T1855 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1855_ok
def T1854 : Node := Node.split 1 T1855 T1856
theorem T1854_ok : Node.check D_R22222 T1854 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1855_ok T1856_ok
def T1853 : Node := Node.split 3 T1854 T1857
theorem T1853_ok : Node.check D_R22222 T1853 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1854_ok T1857_ok
def T1852 : Node := Node.split 0 T1853 T1860
theorem T1852_ok : Node.check D_R22222 T1852 [((489/512),(163/128)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1853_ok T1860_ok
def T1851 : Node := Node.leaf L1851
theorem T1851_ok : Node.check D_R22222 T1851 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/256),(3645/2048)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1851_ok
def T1850 : Node := Node.split 2 T1851 T1852
theorem T1850_ok : Node.check D_R22222 T1850 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/256),(2025/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1851_ok T1852_ok
def T1849 : Node := Node.leaf L1849
theorem T1849_ok : Node.check D_R22222 T1849 [((489/512),(163/128)),((405/512),(2025/2048)),((405/256),(2025/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1849_ok
def T1848 : Node := Node.split 1 T1849 T1850
theorem T1848_ok : Node.check D_R22222 T1848 [((489/512),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1849_ok T1850_ok
def T1847 : Node := Node.leaf L1847
theorem T1847_ok : Node.check D_R22222 T1847 [((489/512),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L1847_ok
def T1846 : Node := Node.split 3 T1847 T1848
theorem T1846_ok : Node.check D_R22222 T1846 [((489/512),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1847_ok T1848_ok
def T1845 : Node := Node.leaf L1845
theorem T1845_ok : Node.check D_R22222 T1845 [((163/256),(489/512)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1845_ok
def T1844 : Node := Node.split 0 T1845 T1846
theorem T1844_ok : Node.check D_R22222 T1844 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1845_ok T1846_ok
def T1843 : Node := Node.split 2 T1844 T1861
theorem T1843_ok : Node.check D_R22222 T1843 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1844_ok T1861_ok
def T1842 : Node := Node.split 1 T1843 T1878
theorem T1842_ok : Node.check D_R22222 T1842 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1843_ok T1878_ok
def T1841 : Node := Node.split 3 T1842 T1879
theorem T1841_ok : Node.check D_R22222 T1841 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1842_ok T1879_ok
def T1840 : Node := Node.leaf L1840
theorem T1840_ok : Node.check D_R22222 T1840 [((0),(163/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1840_ok
def T1839 : Node := Node.split 0 T1840 T1841
theorem T1839_ok : Node.check D_R22222 T1839 [((0),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1840_ok T1841_ok
def T1838 : Node := Node.split 2 T1839 T1884
theorem T1838_ok : Node.check D_R22222 T1838 [((0),(163/128)),((405/512),(405/256)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1839_ok T1884_ok
def T1837 : Node := Node.leaf L1837
theorem T1837_ok : Node.check D_R22222 T1837 [((0),(163/128)),((0),(405/512)),((405/256),(405/128)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1837_ok
def T1836 : Node := Node.split 1 T1837 T1838
theorem T1836_ok : Node.check D_R22222 T1836 [((0),(163/128)),((0),(405/256)),((405/256),(405/128)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1837_ok T1838_ok
def T1835 : Node := Node.split 3 T1836 T1893
theorem T1835_ok : Node.check D_R22222 T1835 [((0),(163/128)),((0),(405/256)),((405/256),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1836_ok T1893_ok
def T1834 : Node := Node.split 0 T1835 T1932
theorem T1834_ok : Node.check D_R22222 T1834 [((0),(163/64)),((0),(405/256)),((405/256),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1835_ok T1932_ok
def T1833 : Node := Node.leaf L1833
theorem T1833_ok : Node.check D_R22222 T1833 [((489/256),(163/64)),((1215/1024),(405/256)),((405/512),(405/256)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1833_ok
def T1832 : Node := Node.leaf L1832
theorem T1832_ok : Node.check D_R22222 T1832 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/1024),(405/256)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1832_ok
def T1831 : Node := Node.leaf L1831
theorem T1831_ok : Node.check D_R22222 T1831 [((1141/512),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1831_ok
def T1830 : Node := Node.leaf L1830
theorem T1830_ok : Node.check D_R22222 T1830 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((2445/512),(163/32))] = true := Node.check_leaf_of _ _ _ L1830_ok
def T1829 : Node := Node.leaf L1829
theorem T1829_ok : Node.check D_R22222 T1829 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/256),(2445/512))] = true := Node.check_leaf_of _ _ _ L1829_ok
def T1828 : Node := Node.split 3 T1829 T1830
theorem T1828_ok : Node.check D_R22222 T1828 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1829_ok T1830_ok
def T1827 : Node := Node.split 0 T1828 T1831
theorem T1827_ok : Node.check D_R22222 T1827 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1828_ok T1831_ok
def T1826 : Node := Node.split 2 T1827 T1832
theorem T1826_ok : Node.check D_R22222 T1826 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(405/256)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1827_ok T1832_ok
def T1825 : Node := Node.split 1 T1826 T1833
theorem T1825_ok : Node.check D_R22222 T1825 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1826_ok T1833_ok
def T1824 : Node := Node.leaf L1824
theorem T1824_ok : Node.check D_R22222 T1824 [((489/256),(163/64)),((1215/1024),(405/256)),((405/512),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1824_ok
def T1823 : Node := Node.leaf L1823
theorem T1823_ok : Node.check D_R22222 T1823 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1823_ok
def T1822 : Node := Node.leaf L1822
theorem T1822_ok : Node.check D_R22222 T1822 [((1141/512),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1822_ok
def T1821 : Node := Node.leaf L1821
theorem T1821_ok : Node.check D_R22222 T1821 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/512),(1141/256))] = true := Node.check_leaf_of _ _ _ L1821_ok
def T1820 : Node := Node.leaf L1820
theorem T1820_ok : Node.check D_R22222 T1820 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((2119/512),(1141/256))] = true := Node.check_leaf_of _ _ _ L1820_ok
def T1819 : Node := Node.split 2 T1820 T1821
theorem T1819_ok : Node.check D_R22222 T1819 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((2119/512),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1820_ok T1821_ok
def T1818 : Node := Node.leaf L1818
theorem T1818_ok : Node.check D_R22222 T1818 [((489/256),(1141/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((2119/512),(1141/256))] = true := Node.check_leaf_of _ _ _ L1818_ok
def T1817 : Node := Node.split 1 T1818 T1819
theorem T1817_ok : Node.check D_R22222 T1817 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((2119/512),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1818_ok T1819_ok
def T1816 : Node := Node.leaf L1816
theorem T1816_ok : Node.check D_R22222 T1816 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1816_ok
def T1815 : Node := Node.leaf L1815
theorem T1815_ok : Node.check D_R22222 T1815 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1815_ok
def T1814 : Node := Node.leaf L1814
theorem T1814_ok : Node.check D_R22222 T1814 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1814_ok
def T1813 : Node := Node.split 2 T1814 T1815
theorem T1813_ok : Node.check D_R22222 T1813 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1814_ok T1815_ok
def T1812 : Node := Node.split 1 T1813 T1816
theorem T1812_ok : Node.check D_R22222 T1812 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1813_ok T1816_ok
def T1811 : Node := Node.leaf L1811
theorem T1811_ok : Node.check D_R22222 T1811 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1811_ok
def T1810 : Node := Node.leaf L1810
theorem T1810_ok : Node.check D_R22222 T1810 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1810_ok
def T1809 : Node := Node.split 1 T1810 T1811
theorem T1809_ok : Node.check D_R22222 T1809 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1810_ok T1811_ok
def T1808 : Node := Node.split 3 T1809 T1812
theorem T1808_ok : Node.check D_R22222 T1808 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1809_ok T1812_ok
def T1807 : Node := Node.leaf L1807
theorem T1807_ok : Node.check D_R22222 T1807 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1807_ok
def T1806 : Node := Node.leaf L1806
theorem T1806_ok : Node.check D_R22222 T1806 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1806_ok
def T1805 : Node := Node.split 2 T1806 T1807
theorem T1805_ok : Node.check D_R22222 T1805 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1806_ok T1807_ok
def T1804 : Node := Node.leaf L1804
theorem T1804_ok : Node.check D_R22222 T1804 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1804_ok
def T1803 : Node := Node.split 1 T1804 T1805
theorem T1803_ok : Node.check D_R22222 T1803 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1804_ok T1805_ok
def T1802 : Node := Node.leaf L1802
theorem T1802_ok : Node.check D_R22222 T1802 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1802_ok
def T1801 : Node := Node.leaf L1801
theorem T1801_ok : Node.check D_R22222 T1801 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1801_ok
def T1800 : Node := Node.split 2 T1801 T1802
theorem T1800_ok : Node.check D_R22222 T1800 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1801_ok T1802_ok
def T1799 : Node := Node.leaf L1799
theorem T1799_ok : Node.check D_R22222 T1799 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1799_ok
def T1798 : Node := Node.split 1 T1799 T1800
theorem T1798_ok : Node.check D_R22222 T1798 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1799_ok T1800_ok
def T1797 : Node := Node.split 3 T1798 T1803
theorem T1797_ok : Node.check D_R22222 T1797 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1798_ok T1803_ok
def T1796 : Node := Node.split 0 T1797 T1808
theorem T1796_ok : Node.check D_R22222 T1796 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1797_ok T1808_ok
def T1795 : Node := Node.leaf L1795
theorem T1795_ok : Node.check D_R22222 T1795 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L1795_ok
def T1794 : Node := Node.split 2 T1795 T1796
theorem T1794_ok : Node.check D_R22222 T1794 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1795_ok T1796_ok
def T1793 : Node := Node.leaf L1793
theorem T1793_ok : Node.check D_R22222 T1793 [((489/256),(1141/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L1793_ok
def T1792 : Node := Node.split 1 T1793 T1794
theorem T1792_ok : Node.check D_R22222 T1792 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1793_ok T1794_ok
def T1791 : Node := Node.split 3 T1792 T1817
theorem T1791_ok : Node.check D_R22222 T1791 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1792_ok T1817_ok
def T1790 : Node := Node.split 0 T1791 T1822
theorem T1790_ok : Node.check D_R22222 T1790 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1791_ok T1822_ok
def T1789 : Node := Node.split 2 T1790 T1823
theorem T1789_ok : Node.check D_R22222 T1789 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1790_ok T1823_ok
def T1788 : Node := Node.split 1 T1789 T1824
theorem T1788_ok : Node.check D_R22222 T1788 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1789_ok T1824_ok
def T1787 : Node := Node.split 3 T1788 T1825
theorem T1787_ok : Node.check D_R22222 T1787 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1788_ok T1825_ok
def T1786 : Node := Node.leaf L1786
theorem T1786_ok : Node.check D_R22222 T1786 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1786_ok
def T1785 : Node := Node.split 0 T1786 T1787
theorem T1785_ok : Node.check D_R22222 T1785 [((163/128),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1786_ok T1787_ok
def T1784 : Node := Node.leaf L1784
theorem T1784_ok : Node.check D_R22222 T1784 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1784_ok
def T1783 : Node := Node.split 2 T1784 T1785
theorem T1783_ok : Node.check D_R22222 T1783 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1784_ok T1785_ok
def T1782 : Node := Node.leaf L1782
theorem T1782_ok : Node.check D_R22222 T1782 [((163/128),(163/64)),((0),(405/512)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1782_ok
def T1781 : Node := Node.split 1 T1782 T1783
theorem T1781_ok : Node.check D_R22222 T1781 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1782_ok T1783_ok
def T1780 : Node := Node.leaf L1780
theorem T1780_ok : Node.check D_R22222 T1780 [((489/256),(163/64)),((1215/1024),(405/256)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1780_ok
def T1779 : Node := Node.leaf L1779
theorem T1779_ok : Node.check D_R22222 T1779 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/1024),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1779_ok
def T1778 : Node := Node.leaf L1778
theorem T1778_ok : Node.check D_R22222 T1778 [((1141/512),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1778_ok
def T1777 : Node := Node.leaf L1777
theorem T1777_ok : Node.check D_R22222 T1777 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1793/512),(489/128))] = true := Node.check_leaf_of _ _ _ L1777_ok
def T1776 : Node := Node.leaf L1776
theorem T1776_ok : Node.check D_R22222 T1776 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/256),(1793/512))] = true := Node.check_leaf_of _ _ _ L1776_ok
def T1775 : Node := Node.leaf L1775
theorem T1775_ok : Node.check D_R22222 T1775 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((815/256),(1793/512))] = true := Node.check_leaf_of _ _ _ L1775_ok
def T1774 : Node := Node.split 2 T1775 T1776
theorem T1774_ok : Node.check D_R22222 T1774 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((815/256),(1793/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1775_ok T1776_ok
def T1773 : Node := Node.leaf L1773
theorem T1773_ok : Node.check D_R22222 T1773 [((489/256),(1141/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((815/256),(1793/512))] = true := Node.check_leaf_of _ _ _ L1773_ok
def T1772 : Node := Node.split 1 T1773 T1774
theorem T1772_ok : Node.check D_R22222 T1772 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/256),(1793/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1773_ok T1774_ok
def T1771 : Node := Node.split 3 T1772 T1777
theorem T1771_ok : Node.check D_R22222 T1771 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1772_ok T1777_ok
def T1770 : Node := Node.split 0 T1771 T1778
theorem T1770_ok : Node.check D_R22222 T1770 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1771_ok T1778_ok
def T1769 : Node := Node.split 2 T1770 T1779
theorem T1769_ok : Node.check D_R22222 T1769 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(405/256)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1770_ok T1779_ok
def T1768 : Node := Node.split 1 T1769 T1780
theorem T1768_ok : Node.check D_R22222 T1768 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1769_ok T1780_ok
def T1767 : Node := Node.leaf L1767
theorem T1767_ok : Node.check D_R22222 T1767 [((489/256),(163/64)),((1215/1024),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1767_ok
def T1766 : Node := Node.leaf L1766
theorem T1766_ok : Node.check D_R22222 T1766 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1766_ok
def T1765 : Node := Node.leaf L1765
theorem T1765_ok : Node.check D_R22222 T1765 [((1141/512),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1765_ok
def T1764 : Node := Node.leaf L1764
theorem T1764_ok : Node.check D_R22222 T1764 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1764_ok
def T1763 : Node := Node.leaf L1763
theorem T1763_ok : Node.check D_R22222 T1763 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1763_ok
def T1762 : Node := Node.leaf L1762
theorem T1762_ok : Node.check D_R22222 T1762 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1762_ok
def T1761 : Node := Node.split 2 T1762 T1763
theorem T1761_ok : Node.check D_R22222 T1761 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1762_ok T1763_ok
def T1760 : Node := Node.split 1 T1761 T1764
theorem T1760_ok : Node.check D_R22222 T1760 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1761_ok T1764_ok
def T1759 : Node := Node.leaf L1759
theorem T1759_ok : Node.check D_R22222 T1759 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1759_ok
def T1758 : Node := Node.leaf L1758
theorem T1758_ok : Node.check D_R22222 T1758 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1758_ok
def T1757 : Node := Node.leaf L1757
theorem T1757_ok : Node.check D_R22222 T1757 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1757_ok
def T1756 : Node := Node.split 2 T1757 T1758
theorem T1756_ok : Node.check D_R22222 T1756 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1757_ok T1758_ok
def T1755 : Node := Node.split 1 T1756 T1759
theorem T1755_ok : Node.check D_R22222 T1755 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1756_ok T1759_ok
def T1754 : Node := Node.split 3 T1755 T1760
theorem T1754_ok : Node.check D_R22222 T1754 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1755_ok T1760_ok
def T1753 : Node := Node.leaf L1753
theorem T1753_ok : Node.check D_R22222 T1753 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1753_ok
def T1752 : Node := Node.leaf L1752
theorem T1752_ok : Node.check D_R22222 T1752 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1752_ok
def T1751 : Node := Node.split 2 T1752 T1753
theorem T1751_ok : Node.check D_R22222 T1751 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1752_ok T1753_ok
def T1750 : Node := Node.leaf L1750
theorem T1750_ok : Node.check D_R22222 T1750 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1750_ok
def T1749 : Node := Node.leaf L1749
theorem T1749_ok : Node.check D_R22222 T1749 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1749_ok
def T1748 : Node := Node.split 2 T1749 T1750
theorem T1748_ok : Node.check D_R22222 T1748 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1749_ok T1750_ok
def T1747 : Node := Node.split 1 T1748 T1751
theorem T1747_ok : Node.check D_R22222 T1747 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1748_ok T1751_ok
def T1746 : Node := Node.leaf L1746
theorem T1746_ok : Node.check D_R22222 T1746 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1746_ok
def T1745 : Node := Node.leaf L1745
theorem T1745_ok : Node.check D_R22222 T1745 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1745_ok
def T1744 : Node := Node.split 2 T1745 T1746
theorem T1744_ok : Node.check D_R22222 T1744 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1745_ok T1746_ok
def T1743 : Node := Node.leaf L1743
theorem T1743_ok : Node.check D_R22222 T1743 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1743_ok
def T1742 : Node := Node.leaf L1742
theorem T1742_ok : Node.check D_R22222 T1742 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1742_ok
def T1741 : Node := Node.split 2 T1742 T1743
theorem T1741_ok : Node.check D_R22222 T1741 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1742_ok T1743_ok
def T1740 : Node := Node.split 1 T1741 T1744
theorem T1740_ok : Node.check D_R22222 T1740 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1741_ok T1744_ok
def T1739 : Node := Node.split 3 T1740 T1747
theorem T1739_ok : Node.check D_R22222 T1739 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1740_ok T1747_ok
def T1738 : Node := Node.split 0 T1739 T1754
theorem T1738_ok : Node.check D_R22222 T1738 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1739_ok T1754_ok
def T1737 : Node := Node.leaf L1737
theorem T1737_ok : Node.check D_R22222 T1737 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1737_ok
def T1736 : Node := Node.split 2 T1737 T1738
theorem T1736_ok : Node.check D_R22222 T1736 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1737_ok T1738_ok
def T1735 : Node := Node.leaf L1735
theorem T1735_ok : Node.check D_R22222 T1735 [((489/256),(1141/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1735_ok
def T1734 : Node := Node.split 1 T1735 T1736
theorem T1734_ok : Node.check D_R22222 T1734 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1735_ok T1736_ok
def T1733 : Node := Node.leaf L1733
theorem T1733_ok : Node.check D_R22222 T1733 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L1733_ok
def T1732 : Node := Node.leaf L1732
theorem T1732_ok : Node.check D_R22222 T1732 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2771/1024),(1467/512))] = true := Node.check_leaf_of _ _ _ L1732_ok
def T1731 : Node := Node.leaf L1731
theorem T1731_ok : Node.check D_R22222 T1731 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2771/1024),(1467/512))] = true := Node.check_leaf_of _ _ _ L1731_ok
def T1730 : Node := Node.split 1 T1731 T1732
theorem T1730_ok : Node.check D_R22222 T1730 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2771/1024),(1467/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1731_ok T1732_ok
def T1729 : Node := Node.leaf L1729
theorem T1729_ok : Node.check D_R22222 T1729 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/64),(2771/1024))] = true := Node.check_leaf_of _ _ _ L1729_ok
def T1728 : Node := Node.split 3 T1729 T1730
theorem T1728_ok : Node.check D_R22222 T1728 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/64),(1467/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1729_ok T1730_ok
def T1727 : Node := Node.split 0 T1728 T1733
theorem T1727_ok : Node.check D_R22222 T1727 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/64),(1467/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1728_ok T1733_ok
def T1726 : Node := Node.leaf L1726
theorem T1726_ok : Node.check D_R22222 T1726 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L1726_ok
def T1725 : Node := Node.split 2 T1726 T1727
theorem T1725_ok : Node.check D_R22222 T1725 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((163/64),(1467/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1726_ok T1727_ok
def T1724 : Node := Node.leaf L1724
theorem T1724_ok : Node.check D_R22222 T1724 [((489/256),(1141/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L1724_ok
def T1723 : Node := Node.split 1 T1724 T1725
theorem T1723_ok : Node.check D_R22222 T1723 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(1467/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1724_ok T1725_ok
def T1722 : Node := Node.split 3 T1723 T1734
theorem T1722_ok : Node.check D_R22222 T1722 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1723_ok T1734_ok
def T1721 : Node := Node.split 0 T1722 T1765
theorem T1721_ok : Node.check D_R22222 T1721 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1722_ok T1765_ok
def T1720 : Node := Node.split 2 T1721 T1766
theorem T1720_ok : Node.check D_R22222 T1720 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1721_ok T1766_ok
def T1719 : Node := Node.split 1 T1720 T1767
theorem T1719_ok : Node.check D_R22222 T1719 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1720_ok T1767_ok
def T1718 : Node := Node.split 3 T1719 T1768
theorem T1718_ok : Node.check D_R22222 T1718 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1719_ok T1768_ok
def T1717 : Node := Node.leaf L1717
theorem T1717_ok : Node.check D_R22222 T1717 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1717_ok
def T1716 : Node := Node.leaf L1716
theorem T1716_ok : Node.check D_R22222 T1716 [((163/128),(489/256)),((1215/1024),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1716_ok
def T1715 : Node := Node.leaf L1715
theorem T1715_ok : Node.check D_R22222 T1715 [((163/128),(489/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1715_ok
def T1714 : Node := Node.leaf L1714
theorem T1714_ok : Node.check D_R22222 T1714 [((815/512),(489/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1714_ok
def T1713 : Node := Node.leaf L1713
theorem T1713_ok : Node.check D_R22222 T1713 [((163/128),(815/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1713_ok
def T1712 : Node := Node.split 0 T1713 T1714
theorem T1712_ok : Node.check D_R22222 T1712 [((163/128),(489/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1713_ok T1714_ok
def T1711 : Node := Node.split 2 T1712 T1715
theorem T1711_ok : Node.check D_R22222 T1711 [((163/128),(489/256)),((405/512),(1215/1024)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1712_ok T1715_ok
def T1710 : Node := Node.split 1 T1711 T1716
theorem T1710_ok : Node.check D_R22222 T1710 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1711_ok T1716_ok
def T1709 : Node := Node.split 3 T1710 T1717
theorem T1709_ok : Node.check D_R22222 T1709 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1710_ok T1717_ok
def T1708 : Node := Node.split 0 T1709 T1718
theorem T1708_ok : Node.check D_R22222 T1708 [((163/128),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1709_ok T1718_ok
def T1707 : Node := Node.leaf L1707
theorem T1707_ok : Node.check D_R22222 T1707 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1707_ok
def T1706 : Node := Node.split 2 T1707 T1708
theorem T1706_ok : Node.check D_R22222 T1706 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1707_ok T1708_ok
def T1705 : Node := Node.leaf L1705
theorem T1705_ok : Node.check D_R22222 T1705 [((163/128),(163/64)),((0),(405/512)),((0),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1705_ok
def T1704 : Node := Node.split 1 T1705 T1706
theorem T1704_ok : Node.check D_R22222 T1704 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1705_ok T1706_ok
def T1703 : Node := Node.split 3 T1704 T1781
theorem T1703_ok : Node.check D_R22222 T1703 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1704_ok T1781_ok
def T1702 : Node := Node.leaf L1702
theorem T1702_ok : Node.check D_R22222 T1702 [((163/256),(163/128)),((1215/1024),(405/256)),((405/512),(405/256)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1702_ok
def T1701 : Node := Node.leaf L1701
theorem T1701_ok : Node.check D_R22222 T1701 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1701_ok
def T1700 : Node := Node.leaf L1700
theorem T1700_ok : Node.check D_R22222 T1700 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2445/512),(163/32))] = true := Node.check_leaf_of _ _ _ L1700_ok
def T1699 : Node := Node.leaf L1699
theorem T1699_ok : Node.check D_R22222 T1699 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((5053/1024),(163/32))] = true := Node.check_leaf_of _ _ _ L1699_ok
def T1698 : Node := Node.leaf L1698
theorem T1698_ok : Node.check D_R22222 T1698 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((5053/1024),(163/32))] = true := Node.check_leaf_of _ _ _ L1698_ok
def T1697 : Node := Node.split 1 T1698 T1699
theorem T1697_ok : Node.check D_R22222 T1697 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((5053/1024),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1698_ok T1699_ok
def T1696 : Node := Node.leaf L1696
theorem T1696_ok : Node.check D_R22222 T1696 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2445/512),(5053/1024))] = true := Node.check_leaf_of _ _ _ L1696_ok
def T1695 : Node := Node.leaf L1695
theorem T1695_ok : Node.check D_R22222 T1695 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2445/512),(5053/1024))] = true := Node.check_leaf_of _ _ _ L1695_ok
def T1694 : Node := Node.split 1 T1695 T1696
theorem T1694_ok : Node.check D_R22222 T1694 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2445/512),(5053/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1695_ok T1696_ok
def T1693 : Node := Node.split 3 T1694 T1697
theorem T1693_ok : Node.check D_R22222 T1693 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2445/512),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1694_ok T1697_ok
def T1692 : Node := Node.split 0 T1693 T1700
theorem T1692_ok : Node.check D_R22222 T1692 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2445/512),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1693_ok T1700_ok
def T1691 : Node := Node.leaf L1691
theorem T1691_ok : Node.check D_R22222 T1691 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((2445/512),(163/32))] = true := Node.check_leaf_of _ _ _ L1691_ok
def T1690 : Node := Node.split 2 T1691 T1692
theorem T1690_ok : Node.check D_R22222 T1690 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((2445/512),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1691_ok T1692_ok
def T1689 : Node := Node.leaf L1689
theorem T1689_ok : Node.check D_R22222 T1689 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((2445/512),(163/32))] = true := Node.check_leaf_of _ _ _ L1689_ok
def T1688 : Node := Node.split 1 T1689 T1690
theorem T1688_ok : Node.check D_R22222 T1688 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((2445/512),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1689_ok T1690_ok
def T1687 : Node := Node.leaf L1687
theorem T1687_ok : Node.check D_R22222 T1687 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/256),(2445/512))] = true := Node.check_leaf_of _ _ _ L1687_ok
def T1686 : Node := Node.split 3 T1687 T1688
theorem T1686_ok : Node.check D_R22222 T1686 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1687_ok T1688_ok
def T1685 : Node := Node.leaf L1685
theorem T1685_ok : Node.check D_R22222 T1685 [((163/256),(489/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/256),(163/32))] = true := Node.check_leaf_of _ _ _ L1685_ok
def T1684 : Node := Node.split 0 T1685 T1686
theorem T1684_ok : Node.check D_R22222 T1684 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1685_ok T1686_ok
def T1683 : Node := Node.split 2 T1684 T1701
theorem T1683_ok : Node.check D_R22222 T1683 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(405/256)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1684_ok T1701_ok
def T1682 : Node := Node.split 1 T1683 T1702
theorem T1682_ok : Node.check D_R22222 T1682 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((1141/256),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1683_ok T1702_ok
def T1681 : Node := Node.leaf L1681
theorem T1681_ok : Node.check D_R22222 T1681 [((163/256),(163/128)),((1215/1024),(405/256)),((405/512),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1681_ok
def T1680 : Node := Node.leaf L1680
theorem T1680_ok : Node.check D_R22222 T1680 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1680_ok
def T1679 : Node := Node.leaf L1679
theorem T1679_ok : Node.check D_R22222 T1679 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/512),(1141/256))] = true := Node.check_leaf_of _ _ _ L1679_ok
def T1678 : Node := Node.leaf L1678
theorem T1678_ok : Node.check D_R22222 T1678 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((4401/1024),(1141/256))] = true := Node.check_leaf_of _ _ _ L1678_ok
def T1677 : Node := Node.leaf L1677
theorem T1677_ok : Node.check D_R22222 T1677 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2119/512),(4401/1024))] = true := Node.check_leaf_of _ _ _ L1677_ok
def T1676 : Node := Node.leaf L1676
theorem T1676_ok : Node.check D_R22222 T1676 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2119/512),(4401/1024))] = true := Node.check_leaf_of _ _ _ L1676_ok
def T1675 : Node := Node.split 1 T1676 T1677
theorem T1675_ok : Node.check D_R22222 T1675 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/512),(4401/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1676_ok T1677_ok
def T1674 : Node := Node.split 3 T1675 T1678
theorem T1674_ok : Node.check D_R22222 T1674 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/512),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1675_ok T1678_ok
def T1673 : Node := Node.split 0 T1674 T1679
theorem T1673_ok : Node.check D_R22222 T1673 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/512),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1674_ok T1679_ok
def T1672 : Node := Node.leaf L1672
theorem T1672_ok : Node.check D_R22222 T1672 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((2119/512),(1141/256))] = true := Node.check_leaf_of _ _ _ L1672_ok
def T1671 : Node := Node.split 2 T1672 T1673
theorem T1671_ok : Node.check D_R22222 T1671 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((2119/512),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1672_ok T1673_ok
def T1670 : Node := Node.leaf L1670
theorem T1670_ok : Node.check D_R22222 T1670 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((2119/512),(1141/256))] = true := Node.check_leaf_of _ _ _ L1670_ok
def T1669 : Node := Node.split 1 T1670 T1671
theorem T1669_ok : Node.check D_R22222 T1669 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((2119/512),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1670_ok T1671_ok
def T1668 : Node := Node.leaf L1668
theorem T1668_ok : Node.check D_R22222 T1668 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L1668_ok
def T1667 : Node := Node.leaf L1667
theorem T1667_ok : Node.check D_R22222 T1667 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1667_ok
def T1666 : Node := Node.leaf L1666
theorem T1666_ok : Node.check D_R22222 T1666 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1666_ok
def T1665 : Node := Node.split 2 T1666 T1667
theorem T1665_ok : Node.check D_R22222 T1665 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1666_ok T1667_ok
def T1664 : Node := Node.leaf L1664
theorem T1664_ok : Node.check D_R22222 T1664 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1664_ok
def T1663 : Node := Node.leaf L1663
theorem T1663_ok : Node.check D_R22222 T1663 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((4075/1024),(2119/512))] = true := Node.check_leaf_of _ _ _ L1663_ok
def T1662 : Node := Node.split 2 T1663 T1664
theorem T1662_ok : Node.check D_R22222 T1662 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1663_ok T1664_ok
def T1661 : Node := Node.split 1 T1662 T1665
theorem T1661_ok : Node.check D_R22222 T1661 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((4075/1024),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1662_ok T1665_ok
def T1660 : Node := Node.leaf L1660
theorem T1660_ok : Node.check D_R22222 T1660 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1660_ok
def T1659 : Node := Node.leaf L1659
theorem T1659_ok : Node.check D_R22222 T1659 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1659_ok
def T1658 : Node := Node.split 2 T1659 T1660
theorem T1658_ok : Node.check D_R22222 T1658 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1659_ok T1660_ok
def T1657 : Node := Node.leaf L1657
theorem T1657_ok : Node.check D_R22222 T1657 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1657_ok
def T1656 : Node := Node.leaf L1656
theorem T1656_ok : Node.check D_R22222 T1656 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/128),(4075/1024))] = true := Node.check_leaf_of _ _ _ L1656_ok
def T1655 : Node := Node.split 2 T1656 T1657
theorem T1655_ok : Node.check D_R22222 T1655 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1656_ok T1657_ok
def T1654 : Node := Node.split 1 T1655 T1658
theorem T1654_ok : Node.check D_R22222 T1654 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(4075/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1655_ok T1658_ok
def T1653 : Node := Node.split 3 T1654 T1661
theorem T1653_ok : Node.check D_R22222 T1653 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1654_ok T1661_ok
def T1652 : Node := Node.split 0 T1653 T1668
theorem T1652_ok : Node.check D_R22222 T1652 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1653_ok T1668_ok
def T1651 : Node := Node.leaf L1651
theorem T1651_ok : Node.check D_R22222 T1651 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L1651_ok
def T1650 : Node := Node.split 2 T1651 T1652
theorem T1650_ok : Node.check D_R22222 T1650 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1651_ok T1652_ok
def T1649 : Node := Node.leaf L1649
theorem T1649_ok : Node.check D_R22222 T1649 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/128),(2119/512))] = true := Node.check_leaf_of _ _ _ L1649_ok
def T1648 : Node := Node.split 1 T1649 T1650
theorem T1648_ok : Node.check D_R22222 T1648 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(2119/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1649_ok T1650_ok
def T1647 : Node := Node.split 3 T1648 T1669
theorem T1647_ok : Node.check D_R22222 T1647 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1648_ok T1669_ok
def T1646 : Node := Node.leaf L1646
theorem T1646_ok : Node.check D_R22222 T1646 [((163/256),(489/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(1141/256))] = true := Node.check_leaf_of _ _ _ L1646_ok
def T1645 : Node := Node.split 0 T1646 T1647
theorem T1645_ok : Node.check D_R22222 T1645 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1646_ok T1647_ok
def T1644 : Node := Node.split 2 T1645 T1680
theorem T1644_ok : Node.check D_R22222 T1644 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1645_ok T1680_ok
def T1643 : Node := Node.split 1 T1644 T1681
theorem T1643_ok : Node.check D_R22222 T1643 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(1141/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1644_ok T1681_ok
def T1642 : Node := Node.split 3 T1643 T1682
theorem T1642_ok : Node.check D_R22222 T1642 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1643_ok T1682_ok
def T1641 : Node := Node.leaf L1641
theorem T1641_ok : Node.check D_R22222 T1641 [((0),(163/256)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1641_ok
def T1640 : Node := Node.split 0 T1641 T1642
theorem T1640_ok : Node.check D_R22222 T1640 [((0),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1641_ok T1642_ok
def T1639 : Node := Node.leaf L1639
theorem T1639_ok : Node.check D_R22222 T1639 [((0),(163/128)),((405/512),(405/256)),((0),(405/512)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1639_ok
def T1638 : Node := Node.split 2 T1639 T1640
theorem T1638_ok : Node.check D_R22222 T1638 [((0),(163/128)),((405/512),(405/256)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1639_ok T1640_ok
def T1637 : Node := Node.leaf L1637
theorem T1637_ok : Node.check D_R22222 T1637 [((0),(163/128)),((0),(405/512)),((0),(405/256)),((489/128),(163/32))] = true := Node.check_leaf_of _ _ _ L1637_ok
def T1636 : Node := Node.split 1 T1637 T1638
theorem T1636_ok : Node.check D_R22222 T1636 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((489/128),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1637_ok T1638_ok
def T1635 : Node := Node.leaf L1635
theorem T1635_ok : Node.check D_R22222 T1635 [((163/256),(163/128)),((1215/1024),(405/256)),((405/512),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1635_ok
def T1634 : Node := Node.leaf L1634
theorem T1634_ok : Node.check D_R22222 T1634 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1634_ok
def T1633 : Node := Node.leaf L1633
theorem T1633_ok : Node.check D_R22222 T1633 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1793/512),(489/128))] = true := Node.check_leaf_of _ _ _ L1633_ok
def T1632 : Node := Node.leaf L1632
theorem T1632_ok : Node.check D_R22222 T1632 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((3749/1024),(489/128))] = true := Node.check_leaf_of _ _ _ L1632_ok
def T1631 : Node := Node.leaf L1631
theorem T1631_ok : Node.check D_R22222 T1631 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((3749/1024),(489/128))] = true := Node.check_leaf_of _ _ _ L1631_ok
def T1630 : Node := Node.split 1 T1631 T1632
theorem T1630_ok : Node.check D_R22222 T1630 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((3749/1024),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1631_ok T1632_ok
def T1629 : Node := Node.leaf L1629
theorem T1629_ok : Node.check D_R22222 T1629 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1793/512),(3749/1024))] = true := Node.check_leaf_of _ _ _ L1629_ok
def T1628 : Node := Node.split 3 T1629 T1630
theorem T1628_ok : Node.check D_R22222 T1628 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1793/512),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1629_ok T1630_ok
def T1627 : Node := Node.split 0 T1628 T1633
theorem T1627_ok : Node.check D_R22222 T1627 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1793/512),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1628_ok T1633_ok
def T1626 : Node := Node.leaf L1626
theorem T1626_ok : Node.check D_R22222 T1626 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((1793/512),(489/128))] = true := Node.check_leaf_of _ _ _ L1626_ok
def T1625 : Node := Node.split 2 T1626 T1627
theorem T1625_ok : Node.check D_R22222 T1625 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((1793/512),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1626_ok T1627_ok
def T1624 : Node := Node.leaf L1624
theorem T1624_ok : Node.check D_R22222 T1624 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((1793/512),(489/128))] = true := Node.check_leaf_of _ _ _ L1624_ok
def T1623 : Node := Node.split 1 T1624 T1625
theorem T1623_ok : Node.check D_R22222 T1623 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1793/512),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1624_ok T1625_ok
def T1622 : Node := Node.leaf L1622
theorem T1622_ok : Node.check D_R22222 T1622 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/256),(1793/512))] = true := Node.check_leaf_of _ _ _ L1622_ok
def T1621 : Node := Node.leaf L1621
theorem T1621_ok : Node.check D_R22222 T1621 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((815/256),(1793/512))] = true := Node.check_leaf_of _ _ _ L1621_ok
def T1620 : Node := Node.split 2 T1621 T1622
theorem T1620_ok : Node.check D_R22222 T1620 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((815/256),(1793/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1621_ok T1622_ok
def T1619 : Node := Node.leaf L1619
theorem T1619_ok : Node.check D_R22222 T1619 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((815/256),(1793/512))] = true := Node.check_leaf_of _ _ _ L1619_ok
def T1618 : Node := Node.split 1 T1619 T1620
theorem T1618_ok : Node.check D_R22222 T1618 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/256),(1793/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1619_ok T1620_ok
def T1617 : Node := Node.split 3 T1618 T1623
theorem T1617_ok : Node.check D_R22222 T1617 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1618_ok T1623_ok
def T1616 : Node := Node.leaf L1616
theorem T1616_ok : Node.check D_R22222 T1616 [((163/256),(489/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/256),(489/128))] = true := Node.check_leaf_of _ _ _ L1616_ok
def T1615 : Node := Node.split 0 T1616 T1617
theorem T1615_ok : Node.check D_R22222 T1615 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1616_ok T1617_ok
def T1614 : Node := Node.split 2 T1615 T1634
theorem T1614_ok : Node.check D_R22222 T1614 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(405/256)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1615_ok T1634_ok
def T1613 : Node := Node.split 1 T1614 T1635
theorem T1613_ok : Node.check D_R22222 T1613 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((815/256),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1614_ok T1635_ok
def T1612 : Node := Node.leaf L1612
theorem T1612_ok : Node.check D_R22222 T1612 [((163/256),(163/128)),((1215/1024),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1612_ok
def T1611 : Node := Node.leaf L1611
theorem T1611_ok : Node.check D_R22222 T1611 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1611_ok
def T1610 : Node := Node.leaf L1610
theorem T1610_ok : Node.check D_R22222 T1610 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1610_ok
def T1609 : Node := Node.leaf L1609
theorem T1609_ok : Node.check D_R22222 T1609 [((1141/1024),(163/128)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1609_ok
def T1608 : Node := Node.leaf L1608
theorem T1608_ok : Node.check D_R22222 T1608 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1608_ok
def T1607 : Node := Node.leaf L1607
theorem T1607_ok : Node.check D_R22222 T1607 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1607_ok
def T1606 : Node := Node.split 2 T1607 T1608
theorem T1606_ok : Node.check D_R22222 T1606 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1607_ok T1608_ok
def T1605 : Node := Node.split 1 T1606 T1609
theorem T1605_ok : Node.check D_R22222 T1605 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1606_ok T1609_ok
def T1604 : Node := Node.split 3 T1605 T1610
theorem T1604_ok : Node.check D_R22222 T1604 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1605_ok T1610_ok
def T1603 : Node := Node.leaf L1603
theorem T1603_ok : Node.check D_R22222 T1603 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1603_ok
def T1602 : Node := Node.leaf L1602
theorem T1602_ok : Node.check D_R22222 T1602 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1602_ok
def T1601 : Node := Node.split 2 T1602 T1603
theorem T1601_ok : Node.check D_R22222 T1601 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1602_ok T1603_ok
def T1600 : Node := Node.leaf L1600
theorem T1600_ok : Node.check D_R22222 T1600 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1600_ok
def T1599 : Node := Node.leaf L1599
theorem T1599_ok : Node.check D_R22222 T1599 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((3097/1024),(815/256))] = true := Node.check_leaf_of _ _ _ L1599_ok
def T1598 : Node := Node.split 2 T1599 T1600
theorem T1598_ok : Node.check D_R22222 T1598 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1599_ok T1600_ok
def T1597 : Node := Node.split 1 T1598 T1601
theorem T1597_ok : Node.check D_R22222 T1597 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((3097/1024),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1598_ok T1601_ok
def T1596 : Node := Node.leaf L1596
theorem T1596_ok : Node.check D_R22222 T1596 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1596_ok
def T1595 : Node := Node.leaf L1595
theorem T1595_ok : Node.check D_R22222 T1595 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1595_ok
def T1594 : Node := Node.split 2 T1595 T1596
theorem T1594_ok : Node.check D_R22222 T1594 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1595_ok T1596_ok
def T1593 : Node := Node.leaf L1593
theorem T1593_ok : Node.check D_R22222 T1593 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1593_ok
def T1592 : Node := Node.leaf L1592
theorem T1592_ok : Node.check D_R22222 T1592 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((1467/512),(3097/1024))] = true := Node.check_leaf_of _ _ _ L1592_ok
def T1591 : Node := Node.split 2 T1592 T1593
theorem T1591_ok : Node.check D_R22222 T1591 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1592_ok T1593_ok
def T1590 : Node := Node.split 1 T1591 T1594
theorem T1590_ok : Node.check D_R22222 T1590 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(3097/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1591_ok T1594_ok
def T1589 : Node := Node.split 3 T1590 T1597
theorem T1589_ok : Node.check D_R22222 T1589 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1590_ok T1597_ok
def T1588 : Node := Node.split 0 T1589 T1604
theorem T1588_ok : Node.check D_R22222 T1588 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1589_ok T1604_ok
def T1587 : Node := Node.leaf L1587
theorem T1587_ok : Node.check D_R22222 T1587 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1587_ok
def T1586 : Node := Node.split 2 T1587 T1588
theorem T1586_ok : Node.check D_R22222 T1586 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1587_ok T1588_ok
def T1585 : Node := Node.leaf L1585
theorem T1585_ok : Node.check D_R22222 T1585 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((1467/512),(815/256))] = true := Node.check_leaf_of _ _ _ L1585_ok
def T1584 : Node := Node.split 1 T1585 T1586
theorem T1584_ok : Node.check D_R22222 T1584 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1467/512),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1585_ok T1586_ok
def T1583 : Node := Node.leaf L1583
theorem T1583_ok : Node.check D_R22222 T1583 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L1583_ok
def T1582 : Node := Node.leaf L1582
theorem T1582_ok : Node.check D_R22222 T1582 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2771/1024),(1467/512))] = true := Node.check_leaf_of _ _ _ L1582_ok
def T1581 : Node := Node.leaf L1581
theorem T1581_ok : Node.check D_R22222 T1581 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2771/1024),(1467/512))] = true := Node.check_leaf_of _ _ _ L1581_ok
def T1580 : Node := Node.split 1 T1581 T1582
theorem T1580_ok : Node.check D_R22222 T1580 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2771/1024),(1467/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1581_ok T1582_ok
def T1579 : Node := Node.leaf L1579
theorem T1579_ok : Node.check D_R22222 T1579 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/64),(2771/1024))] = true := Node.check_leaf_of _ _ _ L1579_ok
def T1578 : Node := Node.split 3 T1579 T1580
theorem T1578_ok : Node.check D_R22222 T1578 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/64),(1467/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1579_ok T1580_ok
def T1577 : Node := Node.split 0 T1578 T1583
theorem T1577_ok : Node.check D_R22222 T1577 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((163/64),(1467/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1578_ok T1583_ok
def T1576 : Node := Node.leaf L1576
theorem T1576_ok : Node.check D_R22222 T1576 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L1576_ok
def T1575 : Node := Node.split 2 T1576 T1577
theorem T1575_ok : Node.check D_R22222 T1575 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((163/64),(1467/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1576_ok T1577_ok
def T1574 : Node := Node.leaf L1574
theorem T1574_ok : Node.check D_R22222 T1574 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((163/64),(1467/512))] = true := Node.check_leaf_of _ _ _ L1574_ok
def T1573 : Node := Node.split 1 T1574 T1575
theorem T1573_ok : Node.check D_R22222 T1573 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(1467/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1574_ok T1575_ok
def T1572 : Node := Node.split 3 T1573 T1584
theorem T1572_ok : Node.check D_R22222 T1572 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1573_ok T1584_ok
def T1571 : Node := Node.leaf L1571
theorem T1571_ok : Node.check D_R22222 T1571 [((163/256),(489/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true := Node.check_leaf_of _ _ _ L1571_ok
def T1570 : Node := Node.split 0 T1571 T1572
theorem T1570_ok : Node.check D_R22222 T1570 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1571_ok T1572_ok
def T1569 : Node := Node.split 2 T1570 T1611
theorem T1569_ok : Node.check D_R22222 T1569 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1570_ok T1611_ok
def T1568 : Node := Node.split 1 T1569 T1612
theorem T1568_ok : Node.check D_R22222 T1568 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(815/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1569_ok T1612_ok
def T1567 : Node := Node.split 3 T1568 T1613
theorem T1567_ok : Node.check D_R22222 T1567 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1568_ok T1613_ok
def T1566 : Node := Node.leaf L1566
theorem T1566_ok : Node.check D_R22222 T1566 [((0),(163/256)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1566_ok
def T1565 : Node := Node.split 0 T1566 T1567
theorem T1565_ok : Node.check D_R22222 T1565 [((0),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1566_ok T1567_ok
def T1564 : Node := Node.leaf L1564
theorem T1564_ok : Node.check D_R22222 T1564 [((0),(163/128)),((405/512),(405/256)),((0),(405/512)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1564_ok
def T1563 : Node := Node.split 2 T1564 T1565
theorem T1563_ok : Node.check D_R22222 T1563 [((0),(163/128)),((405/512),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1564_ok T1565_ok
def T1562 : Node := Node.leaf L1562
theorem T1562_ok : Node.check D_R22222 T1562 [((0),(163/128)),((0),(405/512)),((0),(405/256)),((163/64),(489/128))] = true := Node.check_leaf_of _ _ _ L1562_ok
def T1561 : Node := Node.split 1 T1562 T1563
theorem T1561_ok : Node.check D_R22222 T1561 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((163/64),(489/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1562_ok T1563_ok
def T1560 : Node := Node.split 3 T1561 T1636
theorem T1560_ok : Node.check D_R22222 T1560 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1561_ok T1636_ok
def T1559 : Node := Node.split 0 T1560 T1703
theorem T1559_ok : Node.check D_R22222 T1559 [((0),(163/64)),((0),(405/256)),((0),(405/256)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1560_ok T1703_ok
def T1558 : Node := Node.split 2 T1559 T1834
theorem T1558_ok : Node.check D_R22222 T1558 [((0),(163/64)),((0),(405/256)),((0),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1559_ok T1834_ok
def T1557 : Node := Node.split 1 T1558 T1985
theorem T1557_ok : Node.check D_R22222 T1557 [((0),(163/64)),((0),(405/128)),((0),(405/128)),((163/64),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1558_ok T1985_ok
def T1556 : Node := Node.leaf L1556
theorem T1556_ok : Node.check D_R22222 T1556 [((163/128),(163/64)),((1215/512),(405/128)),((1215/512),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1556_ok
def T1555 : Node := Node.leaf L1555
theorem T1555_ok : Node.check D_R22222 T1555 [((489/256),(163/64)),((1215/512),(405/128)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1555_ok
def T1554 : Node := Node.leaf L1554
theorem T1554_ok : Node.check D_R22222 T1554 [((489/256),(163/64)),((1215/512),(405/128)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1554_ok
def T1553 : Node := Node.split 3 T1554 T1555
theorem T1553_ok : Node.check D_R22222 T1553 [((489/256),(163/64)),((1215/512),(405/128)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1554_ok T1555_ok
def T1552 : Node := Node.leaf L1552
theorem T1552_ok : Node.check D_R22222 T1552 [((163/128),(489/256)),((1215/512),(405/128)),((405/256),(1215/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1552_ok
def T1551 : Node := Node.split 0 T1552 T1553
theorem T1551_ok : Node.check D_R22222 T1551 [((163/128),(163/64)),((1215/512),(405/128)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1552_ok T1553_ok
def T1550 : Node := Node.split 2 T1551 T1556
theorem T1550_ok : Node.check D_R22222 T1550 [((163/128),(163/64)),((1215/512),(405/128)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1551_ok T1556_ok
def T1549 : Node := Node.leaf L1549
theorem T1549_ok : Node.check D_R22222 T1549 [((489/256),(163/64)),((405/256),(1215/512)),((1215/512),(405/128)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1549_ok
def T1548 : Node := Node.leaf L1548
theorem T1548_ok : Node.check D_R22222 T1548 [((489/256),(163/64)),((405/256),(1215/512)),((1215/512),(405/128)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1548_ok
def T1547 : Node := Node.split 3 T1548 T1549
theorem T1547_ok : Node.check D_R22222 T1547 [((489/256),(163/64)),((405/256),(1215/512)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1548_ok T1549_ok
def T1546 : Node := Node.leaf L1546
theorem T1546_ok : Node.check D_R22222 T1546 [((163/128),(489/256)),((405/256),(1215/512)),((1215/512),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1546_ok
def T1545 : Node := Node.split 0 T1546 T1547
theorem T1545_ok : Node.check D_R22222 T1545 [((163/128),(163/64)),((405/256),(1215/512)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1546_ok T1547_ok
def T1544 : Node := Node.leaf L1544
theorem T1544_ok : Node.check D_R22222 T1544 [((489/256),(163/64)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1544_ok
def T1543 : Node := Node.leaf L1543
theorem T1543_ok : Node.check D_R22222 T1543 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1543_ok
def T1542 : Node := Node.split 2 T1543 T1544
theorem T1542_ok : Node.check D_R22222 T1542 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1543_ok T1544_ok
def T1541 : Node := Node.leaf L1541
theorem T1541_ok : Node.check D_R22222 T1541 [((489/256),(163/64)),((405/256),(2025/1024)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1541_ok
def T1540 : Node := Node.split 1 T1541 T1542
theorem T1540_ok : Node.check D_R22222 T1540 [((489/256),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1541_ok T1542_ok
def T1539 : Node := Node.leaf L1539
theorem T1539_ok : Node.check D_R22222 T1539 [((489/256),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1539_ok
def T1538 : Node := Node.split 3 T1539 T1540
theorem T1538_ok : Node.check D_R22222 T1538 [((489/256),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1539_ok T1540_ok
def T1537 : Node := Node.leaf L1537
theorem T1537_ok : Node.check D_R22222 T1537 [((163/128),(489/256)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1537_ok
def T1536 : Node := Node.split 0 T1537 T1538
theorem T1536_ok : Node.check D_R22222 T1536 [((163/128),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1537_ok T1538_ok
def T1535 : Node := Node.split 2 T1536 T1545
theorem T1535_ok : Node.check D_R22222 T1535 [((163/128),(163/64)),((405/256),(1215/512)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1536_ok T1545_ok
def T1534 : Node := Node.split 1 T1535 T1550
theorem T1534_ok : Node.check D_R22222 T1534 [((163/128),(163/64)),((405/256),(405/128)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1535_ok T1550_ok
def T1533 : Node := Node.leaf L1533
theorem T1533_ok : Node.check D_R22222 T1533 [((489/256),(163/64)),((1215/512),(405/128)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1533_ok
def T1532 : Node := Node.leaf L1532
theorem T1532_ok : Node.check D_R22222 T1532 [((489/256),(163/64)),((1215/512),(405/128)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1532_ok
def T1531 : Node := Node.split 3 T1532 T1533
theorem T1531_ok : Node.check D_R22222 T1531 [((489/256),(163/64)),((1215/512),(405/128)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1532_ok T1533_ok
def T1530 : Node := Node.leaf L1530
theorem T1530_ok : Node.check D_R22222 T1530 [((163/128),(489/256)),((1215/512),(405/128)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1530_ok
def T1529 : Node := Node.leaf L1529
theorem T1529_ok : Node.check D_R22222 T1529 [((163/128),(489/256)),((1215/512),(405/128)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1529_ok
def T1528 : Node := Node.split 3 T1529 T1530
theorem T1528_ok : Node.check D_R22222 T1528 [((163/128),(489/256)),((1215/512),(405/128)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1529_ok T1530_ok
def T1527 : Node := Node.split 0 T1528 T1531
theorem T1527_ok : Node.check D_R22222 T1527 [((163/128),(163/64)),((1215/512),(405/128)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1528_ok T1531_ok
def T1526 : Node := Node.leaf L1526
theorem T1526_ok : Node.check D_R22222 T1526 [((489/256),(163/64)),((2835/1024),(405/128)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1526_ok
def T1525 : Node := Node.leaf L1525
theorem T1525_ok : Node.check D_R22222 T1525 [((489/256),(163/64)),((1215/512),(2835/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1525_ok
def T1524 : Node := Node.split 1 T1525 T1526
theorem T1524_ok : Node.check D_R22222 T1524 [((489/256),(163/64)),((1215/512),(405/128)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1525_ok T1526_ok
def T1523 : Node := Node.leaf L1523
theorem T1523_ok : Node.check D_R22222 T1523 [((489/256),(163/64)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1523_ok
def T1522 : Node := Node.split 3 T1523 T1524
theorem T1522_ok : Node.check D_R22222 T1522 [((489/256),(163/64)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1523_ok T1524_ok
def T1521 : Node := Node.leaf L1521
theorem T1521_ok : Node.check D_R22222 T1521 [((163/128),(489/256)),((1215/512),(405/128)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1521_ok
def T1520 : Node := Node.leaf L1520
theorem T1520_ok : Node.check D_R22222 T1520 [((163/128),(489/256)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1520_ok
def T1519 : Node := Node.split 3 T1520 T1521
theorem T1519_ok : Node.check D_R22222 T1519 [((163/128),(489/256)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1520_ok T1521_ok
def T1518 : Node := Node.split 0 T1519 T1522
theorem T1518_ok : Node.check D_R22222 T1518 [((163/128),(163/64)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1519_ok T1522_ok
def T1517 : Node := Node.split 2 T1518 T1527
theorem T1517_ok : Node.check D_R22222 T1517 [((163/128),(163/64)),((1215/512),(405/128)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1518_ok T1527_ok
def T1516 : Node := Node.leaf L1516
theorem T1516_ok : Node.check D_R22222 T1516 [((489/256),(163/64)),((2025/1024),(1215/512)),((2835/1024),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1516_ok
def T1515 : Node := Node.leaf L1515
theorem T1515_ok : Node.check D_R22222 T1515 [((489/256),(163/64)),((2025/1024),(1215/512)),((1215/512),(2835/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1515_ok
def T1514 : Node := Node.split 2 T1515 T1516
theorem T1514_ok : Node.check D_R22222 T1514 [((489/256),(163/64)),((2025/1024),(1215/512)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1515_ok T1516_ok
def T1513 : Node := Node.leaf L1513
theorem T1513_ok : Node.check D_R22222 T1513 [((489/256),(163/64)),((405/256),(2025/1024)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1513_ok
def T1512 : Node := Node.split 1 T1513 T1514
theorem T1512_ok : Node.check D_R22222 T1512 [((489/256),(163/64)),((405/256),(1215/512)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1513_ok T1514_ok
def T1511 : Node := Node.leaf L1511
theorem T1511_ok : Node.check D_R22222 T1511 [((489/256),(163/64)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1511_ok
def T1510 : Node := Node.split 3 T1511 T1512
theorem T1510_ok : Node.check D_R22222 T1510 [((489/256),(163/64)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1511_ok T1512_ok
def T1509 : Node := Node.leaf L1509
theorem T1509_ok : Node.check D_R22222 T1509 [((163/128),(489/256)),((405/256),(1215/512)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1509_ok
def T1508 : Node := Node.leaf L1508
theorem T1508_ok : Node.check D_R22222 T1508 [((163/128),(489/256)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1508_ok
def T1507 : Node := Node.split 3 T1508 T1509
theorem T1507_ok : Node.check D_R22222 T1507 [((163/128),(489/256)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1508_ok T1509_ok
def T1506 : Node := Node.split 0 T1507 T1510
theorem T1506_ok : Node.check D_R22222 T1506 [((163/128),(163/64)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1507_ok T1510_ok
def T1505 : Node := Node.leaf L1505
theorem T1505_ok : Node.check D_R22222 T1505 [((1141/512),(163/64)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1505_ok
def T1504 : Node := Node.leaf L1504
theorem T1504_ok : Node.check D_R22222 T1504 [((489/256),(1141/512)),((4455/2048),(1215/512)),((2025/1024),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1504_ok
def T1503 : Node := Node.leaf L1503
theorem T1503_ok : Node.check D_R22222 T1503 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((4455/2048),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1503_ok
def T1502 : Node := Node.leaf L1502
theorem T1502_ok : Node.check D_R22222 T1502 [((2119/1024),(1141/512)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1502_ok
def T1501 : Node := Node.leaf L1501
theorem T1501_ok : Node.check D_R22222 T1501 [((2119/1024),(1141/512)),((8505/4096),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1501_ok
def T1500 : Node := Node.leaf L1500
theorem T1500_ok : Node.check D_R22222 T1500 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1500_ok
def T1499 : Node := Node.leaf L1499
theorem T1499_ok : Node.check D_R22222 T1499 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1499_ok
def T1498 : Node := Node.split 2 T1499 T1500
theorem T1498_ok : Node.check D_R22222 T1498 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1499_ok T1500_ok
def T1497 : Node := Node.split 1 T1498 T1501
theorem T1497_ok : Node.check D_R22222 T1497 [((2119/1024),(1141/512)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1498_ok T1501_ok
def T1496 : Node := Node.split 3 T1497 T1502
theorem T1496_ok : Node.check D_R22222 T1496 [((2119/1024),(1141/512)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1497_ok T1502_ok
def T1495 : Node := Node.leaf L1495
theorem T1495_ok : Node.check D_R22222 T1495 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1495_ok
def T1494 : Node := Node.leaf L1494
theorem T1494_ok : Node.check D_R22222 T1494 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1494_ok
def T1493 : Node := Node.leaf L1493
theorem T1493_ok : Node.check D_R22222 T1493 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1493_ok
def T1492 : Node := Node.leaf L1492
theorem T1492_ok : Node.check D_R22222 T1492 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1492_ok
def T1491 : Node := Node.split 2 T1492 T1493
theorem T1491_ok : Node.check D_R22222 T1491 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1492_ok T1493_ok
def T1490 : Node := Node.split 1 T1491 T1494
theorem T1490_ok : Node.check D_R22222 T1490 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1491_ok T1494_ok
def T1489 : Node := Node.split 3 T1490 T1495
theorem T1489_ok : Node.check D_R22222 T1489 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1490_ok T1495_ok
def T1488 : Node := Node.split 0 T1489 T1496
theorem T1488_ok : Node.check D_R22222 T1488 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1489_ok T1496_ok
def T1487 : Node := Node.split 2 T1488 T1503
theorem T1487_ok : Node.check D_R22222 T1487 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1488_ok T1503_ok
def T1486 : Node := Node.split 1 T1487 T1504
theorem T1486_ok : Node.check D_R22222 T1486 [((489/256),(1141/512)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1487_ok T1504_ok
def T1485 : Node := Node.leaf L1485
theorem T1485_ok : Node.check D_R22222 T1485 [((489/256),(1141/512)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1485_ok
def T1484 : Node := Node.split 3 T1485 T1486
theorem T1484_ok : Node.check D_R22222 T1484 [((489/256),(1141/512)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1485_ok T1486_ok
def T1483 : Node := Node.split 0 T1484 T1505
theorem T1483_ok : Node.check D_R22222 T1483 [((489/256),(163/64)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1484_ok T1505_ok
def T1482 : Node := Node.leaf L1482
theorem T1482_ok : Node.check D_R22222 T1482 [((1141/512),(163/64)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1482_ok
def T1481 : Node := Node.leaf L1481
theorem T1481_ok : Node.check D_R22222 T1481 [((489/256),(1141/512)),((4455/2048),(1215/512)),((405/256),(2025/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1481_ok
def T1480 : Node := Node.leaf L1480
theorem T1480_ok : Node.check D_R22222 T1480 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1480_ok
def T1479 : Node := Node.leaf L1479
theorem T1479_ok : Node.check D_R22222 T1479 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((405/256),(3645/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1479_ok
def T1478 : Node := Node.split 2 T1479 T1480
theorem T1478_ok : Node.check D_R22222 T1478 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1479_ok T1480_ok
def T1477 : Node := Node.split 1 T1478 T1481
theorem T1477_ok : Node.check D_R22222 T1477 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1478_ok T1481_ok
def T1476 : Node := Node.leaf L1476
theorem T1476_ok : Node.check D_R22222 T1476 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1476_ok
def T1475 : Node := Node.split 3 T1476 T1477
theorem T1475_ok : Node.check D_R22222 T1475 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1476_ok T1477_ok
def T1474 : Node := Node.split 0 T1475 T1482
theorem T1474_ok : Node.check D_R22222 T1474 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1475_ok T1482_ok
def T1473 : Node := Node.split 2 T1474 T1483
theorem T1473_ok : Node.check D_R22222 T1473 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1474_ok T1483_ok
def T1472 : Node := Node.leaf L1472
theorem T1472_ok : Node.check D_R22222 T1472 [((1141/512),(163/64)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1472_ok
def T1471 : Node := Node.leaf L1471
theorem T1471_ok : Node.check D_R22222 T1471 [((489/256),(1141/512)),((3645/2048),(2025/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1471_ok
def T1470 : Node := Node.leaf L1470
theorem T1470_ok : Node.check D_R22222 T1470 [((489/256),(1141/512)),((405/256),(3645/2048)),((2025/1024),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1470_ok
def T1469 : Node := Node.split 1 T1470 T1471
theorem T1469_ok : Node.check D_R22222 T1469 [((489/256),(1141/512)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1470_ok T1471_ok
def T1468 : Node := Node.leaf L1468
theorem T1468_ok : Node.check D_R22222 T1468 [((489/256),(1141/512)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1468_ok
def T1467 : Node := Node.split 3 T1468 T1469
theorem T1467_ok : Node.check D_R22222 T1467 [((489/256),(1141/512)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1468_ok T1469_ok
def T1466 : Node := Node.split 0 T1467 T1472
theorem T1466_ok : Node.check D_R22222 T1466 [((489/256),(163/64)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1467_ok T1472_ok
def T1465 : Node := Node.leaf L1465
theorem T1465_ok : Node.check D_R22222 T1465 [((489/256),(163/64)),((405/256),(2025/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1465_ok
def T1464 : Node := Node.split 2 T1465 T1466
theorem T1464_ok : Node.check D_R22222 T1464 [((489/256),(163/64)),((405/256),(2025/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1465_ok T1466_ok
def T1463 : Node := Node.split 1 T1464 T1473
theorem T1463_ok : Node.check D_R22222 T1463 [((489/256),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1464_ok T1473_ok
def T1462 : Node := Node.leaf L1462
theorem T1462_ok : Node.check D_R22222 T1462 [((489/256),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1462_ok
def T1461 : Node := Node.split 3 T1462 T1463
theorem T1461_ok : Node.check D_R22222 T1461 [((489/256),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1462_ok T1463_ok
def T1460 : Node := Node.leaf L1460
theorem T1460_ok : Node.check D_R22222 T1460 [((163/128),(489/256)),((2025/1024),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1460_ok
def T1459 : Node := Node.leaf L1459
theorem T1459_ok : Node.check D_R22222 T1459 [((163/128),(489/256)),((405/256),(2025/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1459_ok
def T1458 : Node := Node.split 1 T1459 T1460
theorem T1458_ok : Node.check D_R22222 T1458 [((163/128),(489/256)),((405/256),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1459_ok T1460_ok
def T1457 : Node := Node.leaf L1457
theorem T1457_ok : Node.check D_R22222 T1457 [((163/128),(489/256)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1457_ok
def T1456 : Node := Node.split 3 T1457 T1458
theorem T1456_ok : Node.check D_R22222 T1456 [((163/128),(489/256)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1457_ok T1458_ok
def T1455 : Node := Node.split 0 T1456 T1461
theorem T1455_ok : Node.check D_R22222 T1455 [((163/128),(163/64)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1456_ok T1461_ok
def T1454 : Node := Node.split 2 T1455 T1506
theorem T1454_ok : Node.check D_R22222 T1454 [((163/128),(163/64)),((405/256),(1215/512)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1455_ok T1506_ok
def T1453 : Node := Node.split 1 T1454 T1517
theorem T1453_ok : Node.check D_R22222 T1453 [((163/128),(163/64)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1454_ok T1517_ok
def T1452 : Node := Node.split 3 T1453 T1534
theorem T1452_ok : Node.check D_R22222 T1452 [((163/128),(163/64)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1453_ok T1534_ok
def T1451 : Node := Node.leaf L1451
theorem T1451_ok : Node.check D_R22222 T1451 [((163/256),(163/128)),((1215/512),(405/128)),((1215/512),(405/128)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1451_ok
def T1450 : Node := Node.leaf L1450
theorem T1450_ok : Node.check D_R22222 T1450 [((163/256),(163/128)),((1215/512),(405/128)),((1215/512),(405/128)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1450_ok
def T1449 : Node := Node.split 3 T1450 T1451
theorem T1449_ok : Node.check D_R22222 T1449 [((163/256),(163/128)),((1215/512),(405/128)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1450_ok T1451_ok
def T1448 : Node := Node.leaf L1448
theorem T1448_ok : Node.check D_R22222 T1448 [((0),(163/256)),((1215/512),(405/128)),((1215/512),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1448_ok
def T1447 : Node := Node.split 0 T1448 T1449
theorem T1447_ok : Node.check D_R22222 T1447 [((0),(163/128)),((1215/512),(405/128)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1448_ok T1449_ok
def T1446 : Node := Node.leaf L1446
theorem T1446_ok : Node.check D_R22222 T1446 [((163/256),(163/128)),((2835/1024),(405/128)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1446_ok
def T1445 : Node := Node.leaf L1445
theorem T1445_ok : Node.check D_R22222 T1445 [((163/256),(163/128)),((1215/512),(2835/1024)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1445_ok
def T1444 : Node := Node.split 1 T1445 T1446
theorem T1444_ok : Node.check D_R22222 T1444 [((163/256),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1445_ok T1446_ok
def T1443 : Node := Node.leaf L1443
theorem T1443_ok : Node.check D_R22222 T1443 [((163/256),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1443_ok
def T1442 : Node := Node.split 3 T1443 T1444
theorem T1442_ok : Node.check D_R22222 T1442 [((163/256),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1443_ok T1444_ok
def T1441 : Node := Node.leaf L1441
theorem T1441_ok : Node.check D_R22222 T1441 [((0),(163/256)),((1215/512),(405/128)),((405/256),(1215/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1441_ok
def T1440 : Node := Node.split 0 T1441 T1442
theorem T1440_ok : Node.check D_R22222 T1440 [((0),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1441_ok T1442_ok
def T1439 : Node := Node.split 2 T1440 T1447
theorem T1439_ok : Node.check D_R22222 T1439 [((0),(163/128)),((1215/512),(405/128)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1440_ok T1447_ok
def T1438 : Node := Node.leaf L1438
theorem T1438_ok : Node.check D_R22222 T1438 [((163/256),(163/128)),((2025/1024),(1215/512)),((2835/1024),(405/128)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1438_ok
def T1437 : Node := Node.leaf L1437
theorem T1437_ok : Node.check D_R22222 T1437 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/512),(2835/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1437_ok
def T1436 : Node := Node.split 2 T1437 T1438
theorem T1436_ok : Node.check D_R22222 T1436 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/512),(405/128)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1437_ok T1438_ok
def T1435 : Node := Node.leaf L1435
theorem T1435_ok : Node.check D_R22222 T1435 [((163/256),(163/128)),((405/256),(2025/1024)),((1215/512),(405/128)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1435_ok
def T1434 : Node := Node.split 1 T1435 T1436
theorem T1434_ok : Node.check D_R22222 T1434 [((163/256),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1435_ok T1436_ok
def T1433 : Node := Node.leaf L1433
theorem T1433_ok : Node.check D_R22222 T1433 [((163/256),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1433_ok
def T1432 : Node := Node.split 3 T1433 T1434
theorem T1432_ok : Node.check D_R22222 T1432 [((163/256),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1433_ok T1434_ok
def T1431 : Node := Node.leaf L1431
theorem T1431_ok : Node.check D_R22222 T1431 [((0),(163/256)),((405/256),(1215/512)),((1215/512),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1431_ok
def T1430 : Node := Node.split 0 T1431 T1432
theorem T1430_ok : Node.check D_R22222 T1430 [((0),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1431_ok T1432_ok
def T1429 : Node := Node.leaf L1429
theorem T1429_ok : Node.check D_R22222 T1429 [((489/512),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L1429_ok
def T1428 : Node := Node.leaf L1428
theorem T1428_ok : Node.check D_R22222 T1428 [((489/512),(163/128)),((4455/2048),(1215/512)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1428_ok
def T1427 : Node := Node.leaf L1427
theorem T1427_ok : Node.check D_R22222 T1427 [((489/512),(163/128)),((2025/1024),(4455/2048)),((4455/2048),(1215/512)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1427_ok
def T1426 : Node := Node.leaf L1426
theorem T1426_ok : Node.check D_R22222 T1426 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1426_ok
def T1425 : Node := Node.leaf L1425
theorem T1425_ok : Node.check D_R22222 T1425 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1425_ok
def T1424 : Node := Node.leaf L1424
theorem T1424_ok : Node.check D_R22222 T1424 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1424_ok
def T1423 : Node := Node.split 1 T1424 T1425
theorem T1423_ok : Node.check D_R22222 T1423 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1424_ok T1425_ok
def T1422 : Node := Node.leaf L1422
theorem T1422_ok : Node.check D_R22222 T1422 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1422_ok
def T1421 : Node := Node.leaf L1421
theorem T1421_ok : Node.check D_R22222 T1421 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((8505/4096),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1421_ok
def T1420 : Node := Node.leaf L1420
theorem T1420_ok : Node.check D_R22222 T1420 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1420_ok
def T1419 : Node := Node.split 2 T1420 T1421
theorem T1419_ok : Node.check D_R22222 T1419 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1420_ok T1421_ok
def T1418 : Node := Node.split 1 T1419 T1422
theorem T1418_ok : Node.check D_R22222 T1418 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1419_ok T1422_ok
def T1417 : Node := Node.split 3 T1418 T1423
theorem T1417_ok : Node.check D_R22222 T1417 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1418_ok T1423_ok
def T1416 : Node := Node.split 0 T1417 T1426
theorem T1416_ok : Node.check D_R22222 T1416 [((489/512),(163/128)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1417_ok T1426_ok
def T1415 : Node := Node.split 2 T1416 T1427
theorem T1415_ok : Node.check D_R22222 T1415 [((489/512),(163/128)),((2025/1024),(4455/2048)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1416_ok T1427_ok
def T1414 : Node := Node.split 1 T1415 T1428
theorem T1414_ok : Node.check D_R22222 T1414 [((489/512),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1415_ok T1428_ok
def T1413 : Node := Node.split 3 T1414 T1429
theorem T1413_ok : Node.check D_R22222 T1413 [((489/512),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1414_ok T1429_ok
def T1412 : Node := Node.leaf L1412
theorem T1412_ok : Node.check D_R22222 T1412 [((163/256),(489/512)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1412_ok
def T1411 : Node := Node.split 0 T1412 T1413
theorem T1411_ok : Node.check D_R22222 T1411 [((163/256),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1412_ok T1413_ok
def T1410 : Node := Node.leaf L1410
theorem T1410_ok : Node.check D_R22222 T1410 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L1410_ok
def T1409 : Node := Node.leaf L1409
theorem T1409_ok : Node.check D_R22222 T1409 [((489/512),(163/128)),((4455/2048),(1215/512)),((405/256),(2025/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1409_ok
def T1408 : Node := Node.leaf L1408
theorem T1408_ok : Node.check D_R22222 T1408 [((489/512),(163/128)),((2025/1024),(4455/2048)),((3645/2048),(2025/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1408_ok
def T1407 : Node := Node.leaf L1407
theorem T1407_ok : Node.check D_R22222 T1407 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/256),(3645/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1407_ok
def T1406 : Node := Node.split 2 T1407 T1408
theorem T1406_ok : Node.check D_R22222 T1406 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/256),(2025/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1407_ok T1408_ok
def T1405 : Node := Node.split 1 T1406 T1409
theorem T1405_ok : Node.check D_R22222 T1405 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1406_ok T1409_ok
def T1404 : Node := Node.split 3 T1405 T1410
theorem T1404_ok : Node.check D_R22222 T1404 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1405_ok T1410_ok
def T1403 : Node := Node.leaf L1403
theorem T1403_ok : Node.check D_R22222 T1403 [((163/256),(489/512)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1403_ok
def T1402 : Node := Node.split 0 T1403 T1404
theorem T1402_ok : Node.check D_R22222 T1402 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1403_ok T1404_ok
def T1401 : Node := Node.split 2 T1402 T1411
theorem T1401_ok : Node.check D_R22222 T1401 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1402_ok T1411_ok
def T1400 : Node := Node.leaf L1400
theorem T1400_ok : Node.check D_R22222 T1400 [((489/512),(163/128)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L1400_ok
def T1399 : Node := Node.leaf L1399
theorem T1399_ok : Node.check D_R22222 T1399 [((489/512),(163/128)),((3645/2048),(2025/1024)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1399_ok
def T1398 : Node := Node.leaf L1398
theorem T1398_ok : Node.check D_R22222 T1398 [((489/512),(163/128)),((405/256),(3645/2048)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1398_ok
def T1397 : Node := Node.split 1 T1398 T1399
theorem T1397_ok : Node.check D_R22222 T1397 [((489/512),(163/128)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1398_ok T1399_ok
def T1396 : Node := Node.split 3 T1397 T1400
theorem T1396_ok : Node.check D_R22222 T1396 [((489/512),(163/128)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1397_ok T1400_ok
def T1395 : Node := Node.leaf L1395
theorem T1395_ok : Node.check D_R22222 T1395 [((163/256),(489/512)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1395_ok
def T1394 : Node := Node.split 0 T1395 T1396
theorem T1394_ok : Node.check D_R22222 T1394 [((163/256),(163/128)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1395_ok T1396_ok
def T1393 : Node := Node.leaf L1393
theorem T1393_ok : Node.check D_R22222 T1393 [((163/256),(163/128)),((405/256),(2025/1024)),((405/256),(2025/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1393_ok
def T1392 : Node := Node.split 2 T1393 T1394
theorem T1392_ok : Node.check D_R22222 T1392 [((163/256),(163/128)),((405/256),(2025/1024)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1393_ok T1394_ok
def T1391 : Node := Node.split 1 T1392 T1401
theorem T1391_ok : Node.check D_R22222 T1391 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1392_ok T1401_ok
def T1390 : Node := Node.leaf L1390
theorem T1390_ok : Node.check D_R22222 T1390 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1390_ok
def T1389 : Node := Node.leaf L1389
theorem T1389_ok : Node.check D_R22222 T1389 [((163/256),(163/128)),((405/256),(2025/1024)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1389_ok
def T1388 : Node := Node.split 1 T1389 T1390
theorem T1388_ok : Node.check D_R22222 T1388 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1389_ok T1390_ok
def T1387 : Node := Node.split 3 T1388 T1391
theorem T1387_ok : Node.check D_R22222 T1387 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1388_ok T1391_ok
def T1386 : Node := Node.leaf L1386
theorem T1386_ok : Node.check D_R22222 T1386 [((0),(163/256)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1386_ok
def T1385 : Node := Node.split 0 T1386 T1387
theorem T1385_ok : Node.check D_R22222 T1385 [((0),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1386_ok T1387_ok
def T1384 : Node := Node.split 2 T1385 T1430
theorem T1384_ok : Node.check D_R22222 T1384 [((0),(163/128)),((405/256),(1215/512)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1385_ok T1430_ok
def T1383 : Node := Node.split 1 T1384 T1439
theorem T1383_ok : Node.check D_R22222 T1383 [((0),(163/128)),((405/256),(405/128)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1384_ok T1439_ok
def T1382 : Node := Node.leaf L1382
theorem T1382_ok : Node.check D_R22222 T1382 [((163/256),(163/128)),((2835/1024),(405/128)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1382_ok
def T1381 : Node := Node.leaf L1381
theorem T1381_ok : Node.check D_R22222 T1381 [((163/256),(163/128)),((1215/512),(2835/1024)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1381_ok
def T1380 : Node := Node.split 1 T1381 T1382
theorem T1380_ok : Node.check D_R22222 T1380 [((163/256),(163/128)),((1215/512),(405/128)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1381_ok T1382_ok
def T1379 : Node := Node.leaf L1379
theorem T1379_ok : Node.check D_R22222 T1379 [((163/256),(163/128)),((1215/512),(405/128)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1379_ok
def T1378 : Node := Node.split 3 T1379 T1380
theorem T1378_ok : Node.check D_R22222 T1378 [((163/256),(163/128)),((1215/512),(405/128)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1379_ok T1380_ok
def T1377 : Node := Node.leaf L1377
theorem T1377_ok : Node.check D_R22222 T1377 [((0),(163/256)),((1215/512),(405/128)),((1215/512),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L1377_ok
def T1376 : Node := Node.split 0 T1377 T1378
theorem T1376_ok : Node.check D_R22222 T1376 [((0),(163/128)),((1215/512),(405/128)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1377_ok T1378_ok
def T1375 : Node := Node.leaf L1375
theorem T1375_ok : Node.check D_R22222 T1375 [((489/512),(163/128)),((6075/2048),(405/128)),((4455/2048),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1375_ok
def T1374 : Node := Node.leaf L1374
theorem T1374_ok : Node.check D_R22222 T1374 [((1141/1024),(163/128)),((6075/2048),(405/128)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1374_ok
def T1373 : Node := Node.leaf L1373
theorem T1373_ok : Node.check D_R22222 T1373 [((489/512),(1141/1024)),((6075/2048),(405/128)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1373_ok
def T1372 : Node := Node.leaf L1372
theorem T1372_ok : Node.check D_R22222 T1372 [((489/512),(1141/1024)),((6075/2048),(405/128)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1372_ok
def T1371 : Node := Node.split 3 T1372 T1373
theorem T1371_ok : Node.check D_R22222 T1371 [((489/512),(1141/1024)),((6075/2048),(405/128)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1372_ok T1373_ok
def T1370 : Node := Node.split 0 T1371 T1374
theorem T1370_ok : Node.check D_R22222 T1370 [((489/512),(163/128)),((6075/2048),(405/128)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1371_ok T1374_ok
def T1369 : Node := Node.split 2 T1370 T1375
theorem T1369_ok : Node.check D_R22222 T1369 [((489/512),(163/128)),((6075/2048),(405/128)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1370_ok T1375_ok
def T1368 : Node := Node.leaf L1368
theorem T1368_ok : Node.check D_R22222 T1368 [((489/512),(163/128)),((2835/1024),(6075/2048)),((2025/1024),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1368_ok
def T1367 : Node := Node.split 1 T1368 T1369
theorem T1367_ok : Node.check D_R22222 T1367 [((489/512),(163/128)),((2835/1024),(405/128)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1368_ok T1369_ok
def T1366 : Node := Node.leaf L1366
theorem T1366_ok : Node.check D_R22222 T1366 [((489/512),(163/128)),((2835/1024),(405/128)),((2025/1024),(1215/512)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1366_ok
def T1365 : Node := Node.split 3 T1366 T1367
theorem T1365_ok : Node.check D_R22222 T1365 [((489/512),(163/128)),((2835/1024),(405/128)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1366_ok T1367_ok
def T1364 : Node := Node.leaf L1364
theorem T1364_ok : Node.check D_R22222 T1364 [((163/256),(489/512)),((2835/1024),(405/128)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1364_ok
def T1363 : Node := Node.split 0 T1364 T1365
theorem T1363_ok : Node.check D_R22222 T1363 [((163/256),(163/128)),((2835/1024),(405/128)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1364_ok T1365_ok
def T1362 : Node := Node.leaf L1362
theorem T1362_ok : Node.check D_R22222 T1362 [((163/256),(163/128)),((2835/1024),(405/128)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1362_ok
def T1361 : Node := Node.split 2 T1362 T1363
theorem T1361_ok : Node.check D_R22222 T1361 [((163/256),(163/128)),((2835/1024),(405/128)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1362_ok T1363_ok
def T1360 : Node := Node.leaf L1360
theorem T1360_ok : Node.check D_R22222 T1360 [((163/256),(163/128)),((1215/512),(2835/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1360_ok
def T1359 : Node := Node.split 1 T1360 T1361
theorem T1359_ok : Node.check D_R22222 T1359 [((163/256),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1360_ok T1361_ok
def T1358 : Node := Node.leaf L1358
theorem T1358_ok : Node.check D_R22222 T1358 [((163/256),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1358_ok
def T1357 : Node := Node.split 3 T1358 T1359
theorem T1357_ok : Node.check D_R22222 T1357 [((163/256),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1358_ok T1359_ok
def T1356 : Node := Node.leaf L1356
theorem T1356_ok : Node.check D_R22222 T1356 [((0),(163/256)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L1356_ok
def T1355 : Node := Node.split 0 T1356 T1357
theorem T1355_ok : Node.check D_R22222 T1355 [((0),(163/128)),((1215/512),(405/128)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1356_ok T1357_ok
def T1354 : Node := Node.split 2 T1355 T1376
theorem T1354_ok : Node.check D_R22222 T1354 [((0),(163/128)),((1215/512),(405/128)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1355_ok T1376_ok
def T1353 : Node := Node.leaf L1353
theorem T1353_ok : Node.check D_R22222 T1353 [((489/512),(163/128)),((4455/2048),(1215/512)),((2835/1024),(405/128)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1353_ok
def T1352 : Node := Node.leaf L1352
theorem T1352_ok : Node.check D_R22222 T1352 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((6075/2048),(405/128)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1352_ok
def T1351 : Node := Node.leaf L1351
theorem T1351_ok : Node.check D_R22222 T1351 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((6075/2048),(405/128)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1351_ok
def T1350 : Node := Node.leaf L1350
theorem T1350_ok : Node.check D_R22222 T1350 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((6075/2048),(405/128)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1350_ok
def T1349 : Node := Node.split 3 T1350 T1351
theorem T1349_ok : Node.check D_R22222 T1349 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((6075/2048),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1350_ok T1351_ok
def T1348 : Node := Node.split 0 T1349 T1352
theorem T1348_ok : Node.check D_R22222 T1348 [((489/512),(163/128)),((2025/1024),(4455/2048)),((6075/2048),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1349_ok T1352_ok
def T1347 : Node := Node.leaf L1347
theorem T1347_ok : Node.check D_R22222 T1347 [((489/512),(163/128)),((2025/1024),(4455/2048)),((2835/1024),(6075/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1347_ok
def T1346 : Node := Node.split 2 T1347 T1348
theorem T1346_ok : Node.check D_R22222 T1346 [((489/512),(163/128)),((2025/1024),(4455/2048)),((2835/1024),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1347_ok T1348_ok
def T1345 : Node := Node.split 1 T1346 T1353
theorem T1345_ok : Node.check D_R22222 T1345 [((489/512),(163/128)),((2025/1024),(1215/512)),((2835/1024),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1346_ok T1353_ok
def T1344 : Node := Node.leaf L1344
theorem T1344_ok : Node.check D_R22222 T1344 [((489/512),(163/128)),((2025/1024),(1215/512)),((2835/1024),(405/128)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1344_ok
def T1343 : Node := Node.split 3 T1344 T1345
theorem T1343_ok : Node.check D_R22222 T1343 [((489/512),(163/128)),((2025/1024),(1215/512)),((2835/1024),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1344_ok T1345_ok
def T1342 : Node := Node.leaf L1342
theorem T1342_ok : Node.check D_R22222 T1342 [((163/256),(489/512)),((2025/1024),(1215/512)),((2835/1024),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1342_ok
def T1341 : Node := Node.split 0 T1342 T1343
theorem T1341_ok : Node.check D_R22222 T1341 [((163/256),(163/128)),((2025/1024),(1215/512)),((2835/1024),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1342_ok T1343_ok
def T1340 : Node := Node.leaf L1340
theorem T1340_ok : Node.check D_R22222 T1340 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/512),(2835/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1340_ok
def T1339 : Node := Node.split 2 T1340 T1341
theorem T1339_ok : Node.check D_R22222 T1339 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1340_ok T1341_ok
def T1338 : Node := Node.leaf L1338
theorem T1338_ok : Node.check D_R22222 T1338 [((163/256),(163/128)),((405/256),(2025/1024)),((2835/1024),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1338_ok
def T1337 : Node := Node.leaf L1337
theorem T1337_ok : Node.check D_R22222 T1337 [((163/256),(163/128)),((405/256),(2025/1024)),((1215/512),(2835/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1337_ok
def T1336 : Node := Node.split 2 T1337 T1338
theorem T1336_ok : Node.check D_R22222 T1336 [((163/256),(163/128)),((405/256),(2025/1024)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1337_ok T1338_ok
def T1335 : Node := Node.split 1 T1336 T1339
theorem T1335_ok : Node.check D_R22222 T1335 [((163/256),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1336_ok T1339_ok
def T1334 : Node := Node.leaf L1334
theorem T1334_ok : Node.check D_R22222 T1334 [((163/256),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1334_ok
def T1333 : Node := Node.split 3 T1334 T1335
theorem T1333_ok : Node.check D_R22222 T1333 [((163/256),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1334_ok T1335_ok
def T1332 : Node := Node.leaf L1332
theorem T1332_ok : Node.check D_R22222 T1332 [((0),(163/256)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L1332_ok
def T1331 : Node := Node.split 0 T1332 T1333
theorem T1331_ok : Node.check D_R22222 T1331 [((0),(163/128)),((405/256),(1215/512)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1332_ok T1333_ok
def T1330 : Node := Node.leaf L1330
theorem T1330_ok : Node.check D_R22222 T1330 [((489/512),(163/128)),((4455/2048),(1215/512)),((2025/1024),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1330_ok
def T1329 : Node := Node.leaf L1329
theorem T1329_ok : Node.check D_R22222 T1329 [((489/512),(163/128)),((2025/1024),(4455/2048)),((4455/2048),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1329_ok
def T1328 : Node := Node.leaf L1328
theorem T1328_ok : Node.check D_R22222 T1328 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1328_ok
def T1327 : Node := Node.leaf L1327
theorem T1327_ok : Node.check D_R22222 T1327 [((1141/1024),(163/128)),((8505/4096),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1327_ok
def T1326 : Node := Node.leaf L1326
theorem T1326_ok : Node.check D_R22222 T1326 [((1141/1024),(163/128)),((2025/1024),(8505/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1326_ok
def T1325 : Node := Node.leaf L1325
theorem T1325_ok : Node.check D_R22222 T1325 [((1141/1024),(163/128)),((2025/1024),(8505/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1325_ok
def T1324 : Node := Node.split 2 T1325 T1326
theorem T1324_ok : Node.check D_R22222 T1324 [((1141/1024),(163/128)),((2025/1024),(8505/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1325_ok T1326_ok
def T1323 : Node := Node.split 1 T1324 T1327
theorem T1323_ok : Node.check D_R22222 T1323 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1324_ok T1327_ok
def T1322 : Node := Node.split 3 T1323 T1328
theorem T1322_ok : Node.check D_R22222 T1322 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1323_ok T1328_ok
def T1321 : Node := Node.leaf L1321
theorem T1321_ok : Node.check D_R22222 T1321 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1321_ok
def T1320 : Node := Node.leaf L1320
theorem T1320_ok : Node.check D_R22222 T1320 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1320_ok
def T1319 : Node := Node.split 1 T1320 T1321
theorem T1319_ok : Node.check D_R22222 T1319 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1320_ok T1321_ok
def T1318 : Node := Node.leaf L1318
theorem T1318_ok : Node.check D_R22222 T1318 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1318_ok
def T1317 : Node := Node.leaf L1317
theorem T1317_ok : Node.check D_R22222 T1317 [((2119/2048),(1141/1024)),((8505/4096),(4455/2048)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1317_ok
def T1316 : Node := Node.leaf L1316
theorem T1316_ok : Node.check D_R22222 T1316 [((489/512),(2119/2048)),((8505/4096),(4455/2048)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1316_ok
def T1315 : Node := Node.split 0 T1316 T1317
theorem T1315_ok : Node.check D_R22222 T1315 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1316_ok T1317_ok
def T1314 : Node := Node.split 2 T1315 T1318
theorem T1314_ok : Node.check D_R22222 T1314 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1315_ok T1318_ok
def T1313 : Node := Node.leaf L1313
theorem T1313_ok : Node.check D_R22222 T1313 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((8505/4096),(4455/2048)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1313_ok
def T1312 : Node := Node.leaf L1312
theorem T1312_ok : Node.check D_R22222 T1312 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((8505/4096),(4455/2048)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L1312_ok
def T1311 : Node := Node.split 3 T1312 T1313
theorem T1311_ok : Node.check D_R22222 T1311 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1312_ok T1313_ok
def T1310 : Node := Node.leaf L1310
theorem T1310_ok : Node.check D_R22222 T1310 [((489/512),(2119/2048)),((2025/1024),(8505/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1310_ok
def T1309 : Node := Node.split 0 T1310 T1311
theorem T1309_ok : Node.check D_R22222 T1309 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1310_ok T1311_ok
def T1308 : Node := Node.leaf L1308
theorem T1308_ok : Node.check D_R22222 T1308 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1308_ok
def T1307 : Node := Node.split 2 T1308 T1309
theorem T1307_ok : Node.check D_R22222 T1307 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1308_ok T1309_ok
def T1306 : Node := Node.split 1 T1307 T1314
theorem T1306_ok : Node.check D_R22222 T1306 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1307_ok T1314_ok
def T1305 : Node := Node.split 3 T1306 T1319
theorem T1305_ok : Node.check D_R22222 T1305 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1306_ok T1319_ok
def T1304 : Node := Node.split 0 T1305 T1322
theorem T1304_ok : Node.check D_R22222 T1304 [((489/512),(163/128)),((2025/1024),(4455/2048)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1305_ok T1322_ok
def T1303 : Node := Node.split 2 T1304 T1329
theorem T1303_ok : Node.check D_R22222 T1303 [((489/512),(163/128)),((2025/1024),(4455/2048)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1304_ok T1329_ok
def T1302 : Node := Node.split 1 T1303 T1330
theorem T1302_ok : Node.check D_R22222 T1302 [((489/512),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1303_ok T1330_ok
def T1301 : Node := Node.leaf L1301
theorem T1301_ok : Node.check D_R22222 T1301 [((489/512),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1301_ok
def T1300 : Node := Node.split 3 T1301 T1302
theorem T1300_ok : Node.check D_R22222 T1300 [((489/512),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1301_ok T1302_ok
def T1299 : Node := Node.leaf L1299
theorem T1299_ok : Node.check D_R22222 T1299 [((163/256),(489/512)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1299_ok
def T1298 : Node := Node.split 0 T1299 T1300
theorem T1298_ok : Node.check D_R22222 T1298 [((163/256),(163/128)),((2025/1024),(1215/512)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1299_ok T1300_ok
def T1297 : Node := Node.leaf L1297
theorem T1297_ok : Node.check D_R22222 T1297 [((489/512),(163/128)),((4455/2048),(1215/512)),((405/256),(2025/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1297_ok
def T1296 : Node := Node.leaf L1296
theorem T1296_ok : Node.check D_R22222 T1296 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1296_ok
def T1295 : Node := Node.leaf L1295
theorem T1295_ok : Node.check D_R22222 T1295 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1295_ok
def T1294 : Node := Node.leaf L1294
theorem T1294_ok : Node.check D_R22222 T1294 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1294_ok
def T1293 : Node := Node.leaf L1293
theorem T1293_ok : Node.check D_R22222 T1293 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1293_ok
def T1292 : Node := Node.leaf L1292
theorem T1292_ok : Node.check D_R22222 T1292 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((3645/2048),(7695/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1292_ok
def T1291 : Node := Node.split 2 T1292 T1293
theorem T1291_ok : Node.check D_R22222 T1291 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1292_ok T1293_ok
def T1290 : Node := Node.split 1 T1291 T1294
theorem T1290_ok : Node.check D_R22222 T1290 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1291_ok T1294_ok
def T1289 : Node := Node.split 3 T1290 T1295
theorem T1289_ok : Node.check D_R22222 T1289 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1290_ok T1295_ok
def T1288 : Node := Node.split 0 T1289 T1296
theorem T1288_ok : Node.check D_R22222 T1288 [((489/512),(163/128)),((2025/1024),(4455/2048)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1289_ok T1296_ok
def T1287 : Node := Node.leaf L1287
theorem T1287_ok : Node.check D_R22222 T1287 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/256),(3645/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1287_ok
def T1286 : Node := Node.split 2 T1287 T1288
theorem T1286_ok : Node.check D_R22222 T1286 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1287_ok T1288_ok
def T1285 : Node := Node.split 1 T1286 T1297
theorem T1285_ok : Node.check D_R22222 T1285 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1286_ok T1297_ok
def T1284 : Node := Node.leaf L1284
theorem T1284_ok : Node.check D_R22222 T1284 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1284_ok
def T1283 : Node := Node.split 3 T1284 T1285
theorem T1283_ok : Node.check D_R22222 T1283 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1284_ok T1285_ok
def T1282 : Node := Node.leaf L1282
theorem T1282_ok : Node.check D_R22222 T1282 [((163/256),(489/512)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1282_ok
def T1281 : Node := Node.split 0 T1282 T1283
theorem T1281_ok : Node.check D_R22222 T1281 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1282_ok T1283_ok
def T1280 : Node := Node.split 2 T1281 T1298
theorem T1280_ok : Node.check D_R22222 T1280 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1281_ok T1298_ok
def T1279 : Node := Node.leaf L1279
theorem T1279_ok : Node.check D_R22222 T1279 [((489/512),(163/128)),((3645/2048),(2025/1024)),((4455/2048),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1279_ok
def T1278 : Node := Node.leaf L1278
theorem T1278_ok : Node.check D_R22222 T1278 [((1141/1024),(163/128)),((3645/2048),(2025/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1278_ok
def T1277 : Node := Node.leaf L1277
theorem T1277_ok : Node.check D_R22222 T1277 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1277_ok
def T1276 : Node := Node.leaf L1276
theorem T1276_ok : Node.check D_R22222 T1276 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1276_ok
def T1275 : Node := Node.leaf L1275
theorem T1275_ok : Node.check D_R22222 T1275 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1275_ok
def T1274 : Node := Node.split 2 T1275 T1276
theorem T1274_ok : Node.check D_R22222 T1274 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1275_ok T1276_ok
def T1273 : Node := Node.leaf L1273
theorem T1273_ok : Node.check D_R22222 T1273 [((489/512),(1141/1024)),((3645/2048),(7695/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1273_ok
def T1272 : Node := Node.split 1 T1273 T1274
theorem T1272_ok : Node.check D_R22222 T1272 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1273_ok T1274_ok
def T1271 : Node := Node.split 3 T1272 T1277
theorem T1271_ok : Node.check D_R22222 T1271 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1272_ok T1277_ok
def T1270 : Node := Node.split 0 T1271 T1278
theorem T1270_ok : Node.check D_R22222 T1270 [((489/512),(163/128)),((3645/2048),(2025/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1271_ok T1278_ok
def T1269 : Node := Node.split 2 T1270 T1279
theorem T1269_ok : Node.check D_R22222 T1269 [((489/512),(163/128)),((3645/2048),(2025/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1270_ok T1279_ok
def T1268 : Node := Node.leaf L1268
theorem T1268_ok : Node.check D_R22222 T1268 [((489/512),(163/128)),((405/256),(3645/2048)),((2025/1024),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1268_ok
def T1267 : Node := Node.split 1 T1268 T1269
theorem T1267_ok : Node.check D_R22222 T1267 [((489/512),(163/128)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1268_ok T1269_ok
def T1266 : Node := Node.leaf L1266
theorem T1266_ok : Node.check D_R22222 T1266 [((489/512),(163/128)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1266_ok
def T1265 : Node := Node.split 3 T1266 T1267
theorem T1265_ok : Node.check D_R22222 T1265 [((489/512),(163/128)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1266_ok T1267_ok
def T1264 : Node := Node.leaf L1264
theorem T1264_ok : Node.check D_R22222 T1264 [((163/256),(489/512)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1264_ok
def T1263 : Node := Node.split 0 T1264 T1265
theorem T1263_ok : Node.check D_R22222 T1263 [((163/256),(163/128)),((405/256),(2025/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1264_ok T1265_ok
def T1262 : Node := Node.leaf L1262
theorem T1262_ok : Node.check D_R22222 T1262 [((489/512),(163/128)),((3645/2048),(2025/1024)),((405/256),(2025/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1262_ok
def T1261 : Node := Node.leaf L1261
theorem T1261_ok : Node.check D_R22222 T1261 [((489/512),(163/128)),((405/256),(3645/2048)),((405/256),(2025/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1261_ok
def T1260 : Node := Node.split 1 T1261 T1262
theorem T1260_ok : Node.check D_R22222 T1260 [((489/512),(163/128)),((405/256),(2025/1024)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1261_ok T1262_ok
def T1259 : Node := Node.leaf L1259
theorem T1259_ok : Node.check D_R22222 T1259 [((489/512),(163/128)),((405/256),(2025/1024)),((405/256),(2025/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1259_ok
def T1258 : Node := Node.split 3 T1259 T1260
theorem T1258_ok : Node.check D_R22222 T1258 [((489/512),(163/128)),((405/256),(2025/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1259_ok T1260_ok
def T1257 : Node := Node.leaf L1257
theorem T1257_ok : Node.check D_R22222 T1257 [((163/256),(489/512)),((405/256),(2025/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1257_ok
def T1256 : Node := Node.split 0 T1257 T1258
theorem T1256_ok : Node.check D_R22222 T1256 [((163/256),(163/128)),((405/256),(2025/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1257_ok T1258_ok
def T1255 : Node := Node.split 2 T1256 T1263
theorem T1255_ok : Node.check D_R22222 T1255 [((163/256),(163/128)),((405/256),(2025/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1256_ok T1263_ok
def T1254 : Node := Node.split 1 T1255 T1280
theorem T1254_ok : Node.check D_R22222 T1254 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1255_ok T1280_ok
def T1253 : Node := Node.leaf L1253
theorem T1253_ok : Node.check D_R22222 T1253 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1253_ok
def T1252 : Node := Node.split 3 T1253 T1254
theorem T1252_ok : Node.check D_R22222 T1252 [((163/256),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1253_ok T1254_ok
def T1251 : Node := Node.leaf L1251
theorem T1251_ok : Node.check D_R22222 T1251 [((0),(163/256)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L1251_ok
def T1250 : Node := Node.split 0 T1251 T1252
theorem T1250_ok : Node.check D_R22222 T1250 [((0),(163/128)),((405/256),(1215/512)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1251_ok T1252_ok
def T1249 : Node := Node.split 2 T1250 T1331
theorem T1249_ok : Node.check D_R22222 T1249 [((0),(163/128)),((405/256),(1215/512)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1250_ok T1331_ok
def T1248 : Node := Node.split 1 T1249 T1354
theorem T1248_ok : Node.check D_R22222 T1248 [((0),(163/128)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1249_ok T1354_ok
def T1247 : Node := Node.split 3 T1248 T1383
theorem T1247_ok : Node.check D_R22222 T1247 [((0),(163/128)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1248_ok T1383_ok
def T1246 : Node := Node.split 0 T1247 T1452
theorem T1246_ok : Node.check D_R22222 T1246 [((0),(163/64)),((405/256),(405/128)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1247_ok T1452_ok
def T1245 : Node := Node.leaf L1245
theorem T1245_ok : Node.check D_R22222 T1245 [((489/256),(163/64)),((2835/1024),(405/128)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1245_ok
def T1244 : Node := Node.leaf L1244
theorem T1244_ok : Node.check D_R22222 T1244 [((489/256),(163/64)),((2835/1024),(405/128)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1244_ok
def T1243 : Node := Node.split 2 T1244 T1245
theorem T1243_ok : Node.check D_R22222 T1243 [((489/256),(163/64)),((2835/1024),(405/128)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1244_ok T1245_ok
def T1242 : Node := Node.leaf L1242
theorem T1242_ok : Node.check D_R22222 T1242 [((489/256),(163/64)),((1215/512),(2835/1024)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1242_ok
def T1241 : Node := Node.split 1 T1242 T1243
theorem T1241_ok : Node.check D_R22222 T1241 [((489/256),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1242_ok T1243_ok
def T1240 : Node := Node.leaf L1240
theorem T1240_ok : Node.check D_R22222 T1240 [((489/256),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1240_ok
def T1239 : Node := Node.split 3 T1240 T1241
theorem T1239_ok : Node.check D_R22222 T1239 [((489/256),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1240_ok T1241_ok
def T1238 : Node := Node.leaf L1238
theorem T1238_ok : Node.check D_R22222 T1238 [((163/128),(489/256)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1238_ok
def T1237 : Node := Node.split 0 T1238 T1239
theorem T1237_ok : Node.check D_R22222 T1237 [((163/128),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1238_ok T1239_ok
def T1236 : Node := Node.leaf L1236
theorem T1236_ok : Node.check D_R22222 T1236 [((163/128),(163/64)),((1215/512),(405/128)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1236_ok
def T1235 : Node := Node.split 2 T1236 T1237
theorem T1235_ok : Node.check D_R22222 T1235 [((163/128),(163/64)),((1215/512),(405/128)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1236_ok T1237_ok
def T1234 : Node := Node.leaf L1234
theorem T1234_ok : Node.check D_R22222 T1234 [((489/256),(163/64)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1234_ok
def T1233 : Node := Node.leaf L1233
theorem T1233_ok : Node.check D_R22222 T1233 [((1141/512),(163/64)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1233_ok
def T1232 : Node := Node.leaf L1232
theorem T1232_ok : Node.check D_R22222 T1232 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L1232_ok
def T1231 : Node := Node.leaf L1231
theorem T1231_ok : Node.check D_R22222 T1231 [((489/256),(1141/512)),((4455/2048),(1215/512)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1231_ok
def T1230 : Node := Node.leaf L1230
theorem T1230_ok : Node.check D_R22222 T1230 [((2119/1024),(1141/512)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1230_ok
def T1229 : Node := Node.leaf L1229
theorem T1229_ok : Node.check D_R22222 T1229 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1229_ok
def T1228 : Node := Node.leaf L1228
theorem T1228_ok : Node.check D_R22222 T1228 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1228_ok
def T1227 : Node := Node.split 2 T1228 T1229
theorem T1227_ok : Node.check D_R22222 T1227 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1228_ok T1229_ok
def T1226 : Node := Node.split 1 T1227 T1230
theorem T1226_ok : Node.check D_R22222 T1226 [((2119/1024),(1141/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1227_ok T1230_ok
def T1225 : Node := Node.leaf L1225
theorem T1225_ok : Node.check D_R22222 T1225 [((2119/1024),(1141/512)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1225_ok
def T1224 : Node := Node.leaf L1224
theorem T1224_ok : Node.check D_R22222 T1224 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1224_ok
def T1223 : Node := Node.leaf L1223
theorem T1223_ok : Node.check D_R22222 T1223 [((4401/2048),(1141/512)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1223_ok
def T1222 : Node := Node.leaf L1222
theorem T1222_ok : Node.check D_R22222 T1222 [((2119/1024),(4401/2048)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1222_ok
def T1221 : Node := Node.split 0 T1222 T1223
theorem T1221_ok : Node.check D_R22222 T1221 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1222_ok T1223_ok
def T1220 : Node := Node.split 2 T1221 T1224
theorem T1220_ok : Node.check D_R22222 T1220 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1221_ok T1224_ok
def T1219 : Node := Node.split 1 T1220 T1225
theorem T1219_ok : Node.check D_R22222 T1219 [((2119/1024),(1141/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1220_ok T1225_ok
def T1218 : Node := Node.split 3 T1219 T1226
theorem T1218_ok : Node.check D_R22222 T1218 [((2119/1024),(1141/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1219_ok T1226_ok
def T1217 : Node := Node.leaf L1217
theorem T1217_ok : Node.check D_R22222 T1217 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1217_ok
def T1216 : Node := Node.leaf L1216
theorem T1216_ok : Node.check D_R22222 T1216 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1216_ok
def T1215 : Node := Node.leaf L1215
theorem T1215_ok : Node.check D_R22222 T1215 [((4075/2048),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1215_ok
def T1214 : Node := Node.leaf L1214
theorem T1214_ok : Node.check D_R22222 T1214 [((489/256),(4075/2048)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1214_ok
def T1213 : Node := Node.split 0 T1214 T1215
theorem T1213_ok : Node.check D_R22222 T1213 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1214_ok T1215_ok
def T1212 : Node := Node.split 2 T1213 T1216
theorem T1212_ok : Node.check D_R22222 T1212 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1213_ok T1216_ok
def T1211 : Node := Node.split 1 T1212 T1217
theorem T1211_ok : Node.check D_R22222 T1211 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1212_ok T1217_ok
def T1210 : Node := Node.leaf L1210
theorem T1210_ok : Node.check D_R22222 T1210 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1210_ok
def T1209 : Node := Node.leaf L1209
theorem T1209_ok : Node.check D_R22222 T1209 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1209_ok
def T1208 : Node := Node.split 2 T1209 T1210
theorem T1208_ok : Node.check D_R22222 T1208 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1209_ok T1210_ok
def T1207 : Node := Node.leaf L1207
theorem T1207_ok : Node.check D_R22222 T1207 [((4075/2048),(2119/1024)),((16605/8192),(8505/4096)),((4455/4096),(1215/1024)),((4075/2048),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1207_ok
def T1206 : Node := Node.leaf L1206
theorem T1206_ok : Node.check D_R22222 T1206 [((4075/2048),(2119/1024)),((2025/1024),(16605/8192)),((4455/4096),(1215/1024)),((4075/2048),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1206_ok
def T1205 : Node := Node.split 1 T1206 T1207
theorem T1205_ok : Node.check D_R22222 T1205 [((4075/2048),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((4075/2048),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1206_ok T1207_ok
def T1204 : Node := Node.leaf L1204
theorem T1204_ok : Node.check D_R22222 T1204 [((4075/2048),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(4075/2048))] = true := Node.check_leaf_of _ _ _ L1204_ok
def T1203 : Node := Node.split 3 T1204 T1205
theorem T1203_ok : Node.check D_R22222 T1203 [((4075/2048),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1204_ok T1205_ok
def T1202 : Node := Node.leaf L1202
theorem T1202_ok : Node.check D_R22222 T1202 [((489/256),(4075/2048)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1202_ok
def T1201 : Node := Node.split 0 T1202 T1203
theorem T1201_ok : Node.check D_R22222 T1201 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1202_ok T1203_ok
def T1200 : Node := Node.leaf L1200
theorem T1200_ok : Node.check D_R22222 T1200 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1200_ok
def T1199 : Node := Node.split 2 T1200 T1201
theorem T1199_ok : Node.check D_R22222 T1199 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1200_ok T1201_ok
def T1198 : Node := Node.split 1 T1199 T1208
theorem T1198_ok : Node.check D_R22222 T1198 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1199_ok T1208_ok
def T1197 : Node := Node.split 3 T1198 T1211
theorem T1197_ok : Node.check D_R22222 T1197 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1198_ok T1211_ok
def T1196 : Node := Node.split 0 T1197 T1218
theorem T1196_ok : Node.check D_R22222 T1196 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1197_ok T1218_ok
def T1195 : Node := Node.leaf L1195
theorem T1195_ok : Node.check D_R22222 T1195 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1195_ok
def T1194 : Node := Node.split 2 T1195 T1196
theorem T1194_ok : Node.check D_R22222 T1194 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1195_ok T1196_ok
def T1193 : Node := Node.split 1 T1194 T1231
theorem T1193_ok : Node.check D_R22222 T1193 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1194_ok T1231_ok
def T1192 : Node := Node.split 3 T1193 T1232
theorem T1192_ok : Node.check D_R22222 T1192 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1193_ok T1232_ok
def T1191 : Node := Node.split 0 T1192 T1233
theorem T1191_ok : Node.check D_R22222 T1191 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1192_ok T1233_ok
def T1190 : Node := Node.split 2 T1191 T1234
theorem T1190_ok : Node.check D_R22222 T1190 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1191_ok T1234_ok
def T1189 : Node := Node.leaf L1189
theorem T1189_ok : Node.check D_R22222 T1189 [((489/256),(163/64)),((405/256),(2025/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1189_ok
def T1188 : Node := Node.leaf L1188
theorem T1188_ok : Node.check D_R22222 T1188 [((1141/512),(163/64)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1188_ok
def T1187 : Node := Node.leaf L1187
theorem T1187_ok : Node.check D_R22222 T1187 [((489/256),(1141/512)),((405/256),(2025/1024)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L1187_ok
def T1186 : Node := Node.leaf L1186
theorem T1186_ok : Node.check D_R22222 T1186 [((2119/1024),(1141/512)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1186_ok
def T1185 : Node := Node.leaf L1185
theorem T1185_ok : Node.check D_R22222 T1185 [((489/256),(2119/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1185_ok
def T1184 : Node := Node.leaf L1184
theorem T1184_ok : Node.check D_R22222 T1184 [((489/256),(2119/1024)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1184_ok
def T1183 : Node := Node.leaf L1183
theorem T1183_ok : Node.check D_R22222 T1183 [((489/256),(2119/1024)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1183_ok
def T1182 : Node := Node.split 1 T1183 T1184
theorem T1182_ok : Node.check D_R22222 T1182 [((489/256),(2119/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1183_ok T1184_ok
def T1181 : Node := Node.split 3 T1182 T1185
theorem T1181_ok : Node.check D_R22222 T1181 [((489/256),(2119/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1182_ok T1185_ok
def T1180 : Node := Node.split 0 T1181 T1186
theorem T1180_ok : Node.check D_R22222 T1180 [((489/256),(1141/512)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1181_ok T1186_ok
def T1179 : Node := Node.leaf L1179
theorem T1179_ok : Node.check D_R22222 T1179 [((489/256),(1141/512)),((3645/2048),(2025/1024)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1179_ok
def T1178 : Node := Node.split 2 T1179 T1180
theorem T1178_ok : Node.check D_R22222 T1178 [((489/256),(1141/512)),((3645/2048),(2025/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1179_ok T1180_ok
def T1177 : Node := Node.leaf L1177
theorem T1177_ok : Node.check D_R22222 T1177 [((489/256),(1141/512)),((405/256),(3645/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1177_ok
def T1176 : Node := Node.split 1 T1177 T1178
theorem T1176_ok : Node.check D_R22222 T1176 [((489/256),(1141/512)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1177_ok T1178_ok
def T1175 : Node := Node.split 3 T1176 T1187
theorem T1175_ok : Node.check D_R22222 T1175 [((489/256),(1141/512)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1176_ok T1187_ok
def T1174 : Node := Node.split 0 T1175 T1188
theorem T1174_ok : Node.check D_R22222 T1174 [((489/256),(163/64)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1175_ok T1188_ok
def T1173 : Node := Node.split 2 T1174 T1189
theorem T1173_ok : Node.check D_R22222 T1173 [((489/256),(163/64)),((405/256),(2025/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1174_ok T1189_ok
def T1172 : Node := Node.split 1 T1173 T1190
theorem T1172_ok : Node.check D_R22222 T1172 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1173_ok T1190_ok
def T1171 : Node := Node.leaf L1171
theorem T1171_ok : Node.check D_R22222 T1171 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1171_ok
def T1170 : Node := Node.leaf L1170
theorem T1170_ok : Node.check D_R22222 T1170 [((489/256),(163/64)),((405/256),(2025/1024)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1170_ok
def T1169 : Node := Node.split 1 T1170 T1171
theorem T1169_ok : Node.check D_R22222 T1169 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1170_ok T1171_ok
def T1168 : Node := Node.split 3 T1169 T1172
theorem T1168_ok : Node.check D_R22222 T1168 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1169_ok T1172_ok
def T1167 : Node := Node.leaf L1167
theorem T1167_ok : Node.check D_R22222 T1167 [((163/128),(489/256)),((2025/1024),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1167_ok
def T1166 : Node := Node.leaf L1166
theorem T1166_ok : Node.check D_R22222 T1166 [((163/128),(489/256)),((405/256),(2025/1024)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1166_ok
def T1165 : Node := Node.split 1 T1166 T1167
theorem T1165_ok : Node.check D_R22222 T1165 [((163/128),(489/256)),((405/256),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1166_ok T1167_ok
def T1164 : Node := Node.leaf L1164
theorem T1164_ok : Node.check D_R22222 T1164 [((163/128),(489/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L1164_ok
def T1163 : Node := Node.split 3 T1164 T1165
theorem T1163_ok : Node.check D_R22222 T1163 [((163/128),(489/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1164_ok T1165_ok
def T1162 : Node := Node.split 0 T1163 T1168
theorem T1162_ok : Node.check D_R22222 T1162 [((163/128),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1163_ok T1168_ok
def T1161 : Node := Node.leaf L1161
theorem T1161_ok : Node.check D_R22222 T1161 [((163/128),(163/64)),((405/256),(1215/512)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L1161_ok
def T1160 : Node := Node.split 2 T1161 T1162
theorem T1160_ok : Node.check D_R22222 T1160 [((163/128),(163/64)),((405/256),(1215/512)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1161_ok T1162_ok
def T1159 : Node := Node.split 1 T1160 T1235
theorem T1159_ok : Node.check D_R22222 T1159 [((163/128),(163/64)),((405/256),(405/128)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1160_ok T1235_ok
def T1158 : Node := Node.leaf L1158
theorem T1158_ok : Node.check D_R22222 T1158 [((489/256),(163/64)),((2835/1024),(405/128)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1158_ok
def T1157 : Node := Node.leaf L1157
theorem T1157_ok : Node.check D_R22222 T1157 [((1141/512),(163/64)),((2835/1024),(405/128)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1157_ok
def T1156 : Node := Node.leaf L1156
theorem T1156_ok : Node.check D_R22222 T1156 [((2119/1024),(1141/512)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1156_ok
def T1155 : Node := Node.leaf L1155
theorem T1155_ok : Node.check D_R22222 T1155 [((2119/1024),(1141/512)),((12555/4096),(405/128)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1155_ok
def T1154 : Node := Node.leaf L1154
theorem T1154_ok : Node.check D_R22222 T1154 [((2119/1024),(1141/512)),((6075/2048),(12555/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1154_ok
def T1153 : Node := Node.leaf L1153
theorem T1153_ok : Node.check D_R22222 T1153 [((2119/1024),(1141/512)),((6075/2048),(12555/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1153_ok
def T1152 : Node := Node.split 2 T1153 T1154
theorem T1152_ok : Node.check D_R22222 T1152 [((2119/1024),(1141/512)),((6075/2048),(12555/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1153_ok T1154_ok
def T1151 : Node := Node.split 1 T1152 T1155
theorem T1151_ok : Node.check D_R22222 T1151 [((2119/1024),(1141/512)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1152_ok T1155_ok
def T1150 : Node := Node.split 3 T1151 T1156
theorem T1150_ok : Node.check D_R22222 T1150 [((2119/1024),(1141/512)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1151_ok T1156_ok
def T1149 : Node := Node.leaf L1149
theorem T1149_ok : Node.check D_R22222 T1149 [((489/256),(2119/1024)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1149_ok
def T1148 : Node := Node.leaf L1148
theorem T1148_ok : Node.check D_R22222 T1148 [((489/256),(2119/1024)),((12555/4096),(405/128)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1148_ok
def T1147 : Node := Node.leaf L1147
theorem T1147_ok : Node.check D_R22222 T1147 [((489/256),(2119/1024)),((12555/4096),(405/128)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1147_ok
def T1146 : Node := Node.split 2 T1147 T1148
theorem T1146_ok : Node.check D_R22222 T1146 [((489/256),(2119/1024)),((12555/4096),(405/128)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1147_ok T1148_ok
def T1145 : Node := Node.leaf L1145
theorem T1145_ok : Node.check D_R22222 T1145 [((489/256),(2119/1024)),((6075/2048),(12555/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1145_ok
def T1144 : Node := Node.leaf L1144
theorem T1144_ok : Node.check D_R22222 T1144 [((489/256),(2119/1024)),((6075/2048),(12555/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1144_ok
def T1143 : Node := Node.split 2 T1144 T1145
theorem T1143_ok : Node.check D_R22222 T1143 [((489/256),(2119/1024)),((6075/2048),(12555/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1144_ok T1145_ok
def T1142 : Node := Node.split 1 T1143 T1146
theorem T1142_ok : Node.check D_R22222 T1142 [((489/256),(2119/1024)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1143_ok T1146_ok
def T1141 : Node := Node.split 3 T1142 T1149
theorem T1141_ok : Node.check D_R22222 T1141 [((489/256),(2119/1024)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1142_ok T1149_ok
def T1140 : Node := Node.split 0 T1141 T1150
theorem T1140_ok : Node.check D_R22222 T1140 [((489/256),(1141/512)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1141_ok T1150_ok
def T1139 : Node := Node.leaf L1139
theorem T1139_ok : Node.check D_R22222 T1139 [((489/256),(1141/512)),((6075/2048),(405/128)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1139_ok
def T1138 : Node := Node.split 2 T1139 T1140
theorem T1138_ok : Node.check D_R22222 T1138 [((489/256),(1141/512)),((6075/2048),(405/128)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1139_ok T1140_ok
def T1137 : Node := Node.leaf L1137
theorem T1137_ok : Node.check D_R22222 T1137 [((2119/1024),(1141/512)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1137_ok
def T1136 : Node := Node.leaf L1136
theorem T1136_ok : Node.check D_R22222 T1136 [((2119/1024),(1141/512)),((11745/4096),(6075/2048)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1136_ok
def T1135 : Node := Node.leaf L1135
theorem T1135_ok : Node.check D_R22222 T1135 [((2119/1024),(1141/512)),((11745/4096),(6075/2048)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1135_ok
def T1134 : Node := Node.split 2 T1135 T1136
theorem T1134_ok : Node.check D_R22222 T1134 [((2119/1024),(1141/512)),((11745/4096),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1135_ok T1136_ok
def T1133 : Node := Node.leaf L1133
theorem T1133_ok : Node.check D_R22222 T1133 [((2119/1024),(1141/512)),((2835/1024),(11745/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1133_ok
def T1132 : Node := Node.split 1 T1133 T1134
theorem T1132_ok : Node.check D_R22222 T1132 [((2119/1024),(1141/512)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1133_ok T1134_ok
def T1131 : Node := Node.split 3 T1132 T1137
theorem T1131_ok : Node.check D_R22222 T1131 [((2119/1024),(1141/512)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1132_ok T1137_ok
def T1130 : Node := Node.leaf L1130
theorem T1130_ok : Node.check D_R22222 T1130 [((489/256),(2119/1024)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1130_ok
def T1129 : Node := Node.leaf L1129
theorem T1129_ok : Node.check D_R22222 T1129 [((489/256),(2119/1024)),((11745/4096),(6075/2048)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1129_ok
def T1128 : Node := Node.leaf L1128
theorem T1128_ok : Node.check D_R22222 T1128 [((489/256),(2119/1024)),((11745/4096),(6075/2048)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1128_ok
def T1127 : Node := Node.split 2 T1128 T1129
theorem T1127_ok : Node.check D_R22222 T1127 [((489/256),(2119/1024)),((11745/4096),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1128_ok T1129_ok
def T1126 : Node := Node.leaf L1126
theorem T1126_ok : Node.check D_R22222 T1126 [((489/256),(2119/1024)),((2835/1024),(11745/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1126_ok
def T1125 : Node := Node.split 1 T1126 T1127
theorem T1125_ok : Node.check D_R22222 T1125 [((489/256),(2119/1024)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1126_ok T1127_ok
def T1124 : Node := Node.split 3 T1125 T1130
theorem T1124_ok : Node.check D_R22222 T1124 [((489/256),(2119/1024)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1125_ok T1130_ok
def T1123 : Node := Node.split 0 T1124 T1131
theorem T1123_ok : Node.check D_R22222 T1123 [((489/256),(1141/512)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1124_ok T1131_ok
def T1122 : Node := Node.leaf L1122
theorem T1122_ok : Node.check D_R22222 T1122 [((489/256),(1141/512)),((2835/1024),(6075/2048)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1122_ok
def T1121 : Node := Node.split 2 T1122 T1123
theorem T1121_ok : Node.check D_R22222 T1121 [((489/256),(1141/512)),((2835/1024),(6075/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1122_ok T1123_ok
def T1120 : Node := Node.split 1 T1121 T1138
theorem T1120_ok : Node.check D_R22222 T1120 [((489/256),(1141/512)),((2835/1024),(405/128)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1121_ok T1138_ok
def T1119 : Node := Node.leaf L1119
theorem T1119_ok : Node.check D_R22222 T1119 [((489/256),(1141/512)),((2835/1024),(405/128)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1119_ok
def T1118 : Node := Node.split 3 T1119 T1120
theorem T1118_ok : Node.check D_R22222 T1118 [((489/256),(1141/512)),((2835/1024),(405/128)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1119_ok T1120_ok
def T1117 : Node := Node.split 0 T1118 T1157
theorem T1117_ok : Node.check D_R22222 T1117 [((489/256),(163/64)),((2835/1024),(405/128)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1118_ok T1157_ok
def T1116 : Node := Node.split 2 T1117 T1158
theorem T1116_ok : Node.check D_R22222 T1116 [((489/256),(163/64)),((2835/1024),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1117_ok T1158_ok
def T1115 : Node := Node.leaf L1115
theorem T1115_ok : Node.check D_R22222 T1115 [((489/256),(163/64)),((1215/512),(2835/1024)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1115_ok
def T1114 : Node := Node.split 1 T1115 T1116
theorem T1114_ok : Node.check D_R22222 T1114 [((489/256),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1115_ok T1116_ok
def T1113 : Node := Node.leaf L1113
theorem T1113_ok : Node.check D_R22222 T1113 [((489/256),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1113_ok
def T1112 : Node := Node.split 3 T1113 T1114
theorem T1112_ok : Node.check D_R22222 T1112 [((489/256),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1113_ok T1114_ok
def T1111 : Node := Node.leaf L1111
theorem T1111_ok : Node.check D_R22222 T1111 [((163/128),(489/256)),((2835/1024),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1111_ok
def T1110 : Node := Node.leaf L1110
theorem T1110_ok : Node.check D_R22222 T1110 [((163/128),(489/256)),((1215/512),(2835/1024)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1110_ok
def T1109 : Node := Node.split 1 T1110 T1111
theorem T1109_ok : Node.check D_R22222 T1109 [((163/128),(489/256)),((1215/512),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1110_ok T1111_ok
def T1108 : Node := Node.leaf L1108
theorem T1108_ok : Node.check D_R22222 T1108 [((163/128),(489/256)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1108_ok
def T1107 : Node := Node.split 3 T1108 T1109
theorem T1107_ok : Node.check D_R22222 T1107 [((163/128),(489/256)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1108_ok T1109_ok
def T1106 : Node := Node.split 0 T1107 T1112
theorem T1106_ok : Node.check D_R22222 T1106 [((163/128),(163/64)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1107_ok T1112_ok
def T1105 : Node := Node.leaf L1105
theorem T1105_ok : Node.check D_R22222 T1105 [((163/128),(163/64)),((1215/512),(405/128)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L1105_ok
def T1104 : Node := Node.split 2 T1105 T1106
theorem T1104_ok : Node.check D_R22222 T1104 [((163/128),(163/64)),((1215/512),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1105_ok T1106_ok
def T1103 : Node := Node.leaf L1103
theorem T1103_ok : Node.check D_R22222 T1103 [((489/256),(163/64)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1103_ok
def T1102 : Node := Node.leaf L1102
theorem T1102_ok : Node.check D_R22222 T1102 [((1141/512),(163/64)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1102_ok
def T1101 : Node := Node.leaf L1101
theorem T1101_ok : Node.check D_R22222 T1101 [((489/256),(1141/512)),((4455/2048),(1215/512)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1101_ok
def T1100 : Node := Node.leaf L1100
theorem T1100_ok : Node.check D_R22222 T1100 [((2119/1024),(1141/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1100_ok
def T1099 : Node := Node.leaf L1099
theorem T1099_ok : Node.check D_R22222 T1099 [((2119/1024),(1141/512)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1099_ok
def T1098 : Node := Node.leaf L1098
theorem T1098_ok : Node.check D_R22222 T1098 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1098_ok
def T1097 : Node := Node.leaf L1097
theorem T1097_ok : Node.check D_R22222 T1097 [((4401/2048),(1141/512)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1097_ok
def T1096 : Node := Node.leaf L1096
theorem T1096_ok : Node.check D_R22222 T1096 [((2119/1024),(4401/2048)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1096_ok
def T1095 : Node := Node.split 0 T1096 T1097
theorem T1095_ok : Node.check D_R22222 T1095 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1096_ok T1097_ok
def T1094 : Node := Node.split 2 T1095 T1098
theorem T1094_ok : Node.check D_R22222 T1094 [((2119/1024),(1141/512)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1095_ok T1098_ok
def T1093 : Node := Node.split 1 T1094 T1099
theorem T1093_ok : Node.check D_R22222 T1093 [((2119/1024),(1141/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1094_ok T1099_ok
def T1092 : Node := Node.split 3 T1093 T1100
theorem T1092_ok : Node.check D_R22222 T1092 [((2119/1024),(1141/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1093_ok T1100_ok
def T1091 : Node := Node.leaf L1091
theorem T1091_ok : Node.check D_R22222 T1091 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1091_ok
def T1090 : Node := Node.leaf L1090
theorem T1090_ok : Node.check D_R22222 T1090 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1090_ok
def T1089 : Node := Node.leaf L1089
theorem T1089_ok : Node.check D_R22222 T1089 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1089_ok
def T1088 : Node := Node.split 2 T1089 T1090
theorem T1088_ok : Node.check D_R22222 T1088 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1089_ok T1090_ok
def T1087 : Node := Node.split 1 T1088 T1091
theorem T1087_ok : Node.check D_R22222 T1087 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1088_ok T1091_ok
def T1086 : Node := Node.leaf L1086
theorem T1086_ok : Node.check D_R22222 T1086 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1086_ok
def T1085 : Node := Node.leaf L1085
theorem T1085_ok : Node.check D_R22222 T1085 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1085_ok
def T1084 : Node := Node.split 2 T1085 T1086
theorem T1084_ok : Node.check D_R22222 T1084 [((489/256),(2119/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1085_ok T1086_ok
def T1083 : Node := Node.leaf L1083
theorem T1083_ok : Node.check D_R22222 T1083 [((4075/2048),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1083_ok
def T1082 : Node := Node.leaf L1082
theorem T1082_ok : Node.check D_R22222 T1082 [((4075/2048),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L1082_ok
def T1081 : Node := Node.split 3 T1082 T1083
theorem T1081_ok : Node.check D_R22222 T1081 [((4075/2048),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1082_ok T1083_ok
def T1080 : Node := Node.leaf L1080
theorem T1080_ok : Node.check D_R22222 T1080 [((489/256),(4075/2048)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1080_ok
def T1079 : Node := Node.leaf L1079
theorem T1079_ok : Node.check D_R22222 T1079 [((489/256),(4075/2048)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L1079_ok
def T1078 : Node := Node.split 3 T1079 T1080
theorem T1078_ok : Node.check D_R22222 T1078 [((489/256),(4075/2048)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1079_ok T1080_ok
def T1077 : Node := Node.split 0 T1078 T1081
theorem T1077_ok : Node.check D_R22222 T1077 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1078_ok T1081_ok
def T1076 : Node := Node.leaf L1076
theorem T1076_ok : Node.check D_R22222 T1076 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1076_ok
def T1075 : Node := Node.split 2 T1076 T1077
theorem T1075_ok : Node.check D_R22222 T1075 [((489/256),(2119/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1076_ok T1077_ok
def T1074 : Node := Node.split 1 T1075 T1084
theorem T1074_ok : Node.check D_R22222 T1074 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1075_ok T1084_ok
def T1073 : Node := Node.split 3 T1074 T1087
theorem T1073_ok : Node.check D_R22222 T1073 [((489/256),(2119/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1074_ok T1087_ok
def T1072 : Node := Node.split 0 T1073 T1092
theorem T1072_ok : Node.check D_R22222 T1072 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1073_ok T1092_ok
def T1071 : Node := Node.leaf L1071
theorem T1071_ok : Node.check D_R22222 T1071 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1071_ok
def T1070 : Node := Node.split 2 T1071 T1072
theorem T1070_ok : Node.check D_R22222 T1070 [((489/256),(1141/512)),((2025/1024),(4455/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1071_ok T1072_ok
def T1069 : Node := Node.split 1 T1070 T1101
theorem T1069_ok : Node.check D_R22222 T1069 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1070_ok T1101_ok
def T1068 : Node := Node.leaf L1068
theorem T1068_ok : Node.check D_R22222 T1068 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1068_ok
def T1067 : Node := Node.split 3 T1068 T1069
theorem T1067_ok : Node.check D_R22222 T1067 [((489/256),(1141/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1068_ok T1069_ok
def T1066 : Node := Node.split 0 T1067 T1102
theorem T1066_ok : Node.check D_R22222 T1066 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1067_ok T1102_ok
def T1065 : Node := Node.split 2 T1066 T1103
theorem T1065_ok : Node.check D_R22222 T1065 [((489/256),(163/64)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1066_ok T1103_ok
def T1064 : Node := Node.leaf L1064
theorem T1064_ok : Node.check D_R22222 T1064 [((489/256),(163/64)),((405/256),(2025/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1064_ok
def T1063 : Node := Node.leaf L1063
theorem T1063_ok : Node.check D_R22222 T1063 [((1141/512),(163/64)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1063_ok
def T1062 : Node := Node.leaf L1062
theorem T1062_ok : Node.check D_R22222 T1062 [((2119/1024),(1141/512)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1062_ok
def T1061 : Node := Node.leaf L1061
theorem T1061_ok : Node.check D_R22222 T1061 [((2119/1024),(1141/512)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1061_ok
def T1060 : Node := Node.leaf L1060
theorem T1060_ok : Node.check D_R22222 T1060 [((2119/1024),(1141/512)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1060_ok
def T1059 : Node := Node.split 2 T1060 T1061
theorem T1059_ok : Node.check D_R22222 T1059 [((2119/1024),(1141/512)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1060_ok T1061_ok
def T1058 : Node := Node.leaf L1058
theorem T1058_ok : Node.check D_R22222 T1058 [((2119/1024),(1141/512)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1058_ok
def T1057 : Node := Node.split 1 T1058 T1059
theorem T1057_ok : Node.check D_R22222 T1057 [((2119/1024),(1141/512)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1058_ok T1059_ok
def T1056 : Node := Node.split 3 T1057 T1062
theorem T1056_ok : Node.check D_R22222 T1056 [((2119/1024),(1141/512)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1057_ok T1062_ok
def T1055 : Node := Node.leaf L1055
theorem T1055_ok : Node.check D_R22222 T1055 [((489/256),(2119/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L1055_ok
def T1054 : Node := Node.leaf L1054
theorem T1054_ok : Node.check D_R22222 T1054 [((489/256),(2119/1024)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1054_ok
def T1053 : Node := Node.leaf L1053
theorem T1053_ok : Node.check D_R22222 T1053 [((489/256),(2119/1024)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1053_ok
def T1052 : Node := Node.split 2 T1053 T1054
theorem T1052_ok : Node.check D_R22222 T1052 [((489/256),(2119/1024)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1053_ok T1054_ok
def T1051 : Node := Node.leaf L1051
theorem T1051_ok : Node.check D_R22222 T1051 [((489/256),(2119/1024)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L1051_ok
def T1050 : Node := Node.split 1 T1051 T1052
theorem T1050_ok : Node.check D_R22222 T1050 [((489/256),(2119/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1051_ok T1052_ok
def T1049 : Node := Node.split 3 T1050 T1055
theorem T1049_ok : Node.check D_R22222 T1049 [((489/256),(2119/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1050_ok T1055_ok
def T1048 : Node := Node.split 0 T1049 T1056
theorem T1048_ok : Node.check D_R22222 T1048 [((489/256),(1141/512)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1049_ok T1056_ok
def T1047 : Node := Node.leaf L1047
theorem T1047_ok : Node.check D_R22222 T1047 [((489/256),(1141/512)),((3645/2048),(2025/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1047_ok
def T1046 : Node := Node.split 2 T1047 T1048
theorem T1046_ok : Node.check D_R22222 T1046 [((489/256),(1141/512)),((3645/2048),(2025/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1047_ok T1048_ok
def T1045 : Node := Node.leaf L1045
theorem T1045_ok : Node.check D_R22222 T1045 [((489/256),(1141/512)),((405/256),(3645/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L1045_ok
def T1044 : Node := Node.split 1 T1045 T1046
theorem T1044_ok : Node.check D_R22222 T1044 [((489/256),(1141/512)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1045_ok T1046_ok
def T1043 : Node := Node.leaf L1043
theorem T1043_ok : Node.check D_R22222 T1043 [((489/256),(1141/512)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L1043_ok
def T1042 : Node := Node.split 3 T1043 T1044
theorem T1042_ok : Node.check D_R22222 T1042 [((489/256),(1141/512)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1043_ok T1044_ok
def T1041 : Node := Node.split 0 T1042 T1063
theorem T1041_ok : Node.check D_R22222 T1041 [((489/256),(163/64)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1042_ok T1063_ok
def T1040 : Node := Node.split 2 T1041 T1064
theorem T1040_ok : Node.check D_R22222 T1040 [((489/256),(163/64)),((405/256),(2025/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1041_ok T1064_ok
def T1039 : Node := Node.split 1 T1040 T1065
theorem T1039_ok : Node.check D_R22222 T1039 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1040_ok T1065_ok
def T1038 : Node := Node.leaf L1038
theorem T1038_ok : Node.check D_R22222 T1038 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1038_ok
def T1037 : Node := Node.split 3 T1038 T1039
theorem T1037_ok : Node.check D_R22222 T1037 [((489/256),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1038_ok T1039_ok
def T1036 : Node := Node.leaf L1036
theorem T1036_ok : Node.check D_R22222 T1036 [((163/128),(489/256)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1036_ok
def T1035 : Node := Node.leaf L1035
theorem T1035_ok : Node.check D_R22222 T1035 [((815/512),(489/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1035_ok
def T1034 : Node := Node.leaf L1034
theorem T1034_ok : Node.check D_R22222 T1034 [((163/128),(815/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1034_ok
def T1033 : Node := Node.split 0 T1034 T1035
theorem T1033_ok : Node.check D_R22222 T1033 [((163/128),(489/256)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1034_ok T1035_ok
def T1032 : Node := Node.split 2 T1033 T1036
theorem T1032_ok : Node.check D_R22222 T1032 [((163/128),(489/256)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1033_ok T1036_ok
def T1031 : Node := Node.leaf L1031
theorem T1031_ok : Node.check D_R22222 T1031 [((163/128),(489/256)),((405/256),(2025/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1031_ok
def T1030 : Node := Node.leaf L1030
theorem T1030_ok : Node.check D_R22222 T1030 [((163/128),(489/256)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L1030_ok
def T1029 : Node := Node.split 2 T1030 T1031
theorem T1029_ok : Node.check D_R22222 T1029 [((163/128),(489/256)),((405/256),(2025/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1030_ok T1031_ok
def T1028 : Node := Node.split 1 T1029 T1032
theorem T1028_ok : Node.check D_R22222 T1028 [((163/128),(489/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1029_ok T1032_ok
def T1027 : Node := Node.leaf L1027
theorem T1027_ok : Node.check D_R22222 T1027 [((163/128),(489/256)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L1027_ok
def T1026 : Node := Node.split 3 T1027 T1028
theorem T1026_ok : Node.check D_R22222 T1026 [((163/128),(489/256)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1027_ok T1028_ok
def T1025 : Node := Node.split 0 T1026 T1037
theorem T1025_ok : Node.check D_R22222 T1025 [((163/128),(163/64)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1026_ok T1037_ok
def T1024 : Node := Node.leaf L1024
theorem T1024_ok : Node.check D_R22222 T1024 [((163/128),(163/64)),((405/256),(1215/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L1024_ok
def T1023 : Node := Node.split 2 T1024 T1025
theorem T1023_ok : Node.check D_R22222 T1023 [((163/128),(163/64)),((405/256),(1215/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1024_ok T1025_ok
def T1022 : Node := Node.split 1 T1023 T1104
theorem T1022_ok : Node.check D_R22222 T1022 [((163/128),(163/64)),((405/256),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1023_ok T1104_ok
def T1021 : Node := Node.split 3 T1022 T1159
theorem T1021_ok : Node.check D_R22222 T1021 [((163/128),(163/64)),((405/256),(405/128)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1022_ok T1159_ok
def T1020 : Node := Node.leaf L1020
theorem T1020_ok : Node.check D_R22222 T1020 [((163/256),(163/128)),((2835/1024),(405/128)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L1020_ok
def T1019 : Node := Node.leaf L1019
theorem T1019_ok : Node.check D_R22222 T1019 [((489/512),(163/128)),((2835/1024),(405/128)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L1019_ok
def T1018 : Node := Node.leaf L1018
theorem T1018_ok : Node.check D_R22222 T1018 [((1141/1024),(163/128)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1018_ok
def T1017 : Node := Node.leaf L1017
theorem T1017_ok : Node.check D_R22222 T1017 [((489/512),(1141/1024)),((12555/4096),(405/128)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1017_ok
def T1016 : Node := Node.leaf L1016
theorem T1016_ok : Node.check D_R22222 T1016 [((489/512),(1141/1024)),((6075/2048),(12555/4096)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1016_ok
def T1015 : Node := Node.leaf L1015
theorem T1015_ok : Node.check D_R22222 T1015 [((489/512),(1141/1024)),((6075/2048),(12555/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1015_ok
def T1014 : Node := Node.split 2 T1015 T1016
theorem T1014_ok : Node.check D_R22222 T1014 [((489/512),(1141/1024)),((6075/2048),(12555/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1015_ok T1016_ok
def T1013 : Node := Node.split 1 T1014 T1017
theorem T1013_ok : Node.check D_R22222 T1013 [((489/512),(1141/1024)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1014_ok T1017_ok
def T1012 : Node := Node.leaf L1012
theorem T1012_ok : Node.check D_R22222 T1012 [((489/512),(1141/1024)),((12555/4096),(405/128)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1012_ok
def T1011 : Node := Node.leaf L1011
theorem T1011_ok : Node.check D_R22222 T1011 [((489/512),(1141/1024)),((6075/2048),(12555/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1011_ok
def T1010 : Node := Node.leaf L1010
theorem T1010_ok : Node.check D_R22222 T1010 [((489/512),(1141/1024)),((6075/2048),(12555/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1010_ok
def T1009 : Node := Node.split 2 T1010 T1011
theorem T1009_ok : Node.check D_R22222 T1009 [((489/512),(1141/1024)),((6075/2048),(12555/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1010_ok T1011_ok
def T1008 : Node := Node.split 1 T1009 T1012
theorem T1008_ok : Node.check D_R22222 T1008 [((489/512),(1141/1024)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1009_ok T1012_ok
def T1007 : Node := Node.split 3 T1008 T1013
theorem T1007_ok : Node.check D_R22222 T1007 [((489/512),(1141/1024)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1008_ok T1013_ok
def T1006 : Node := Node.split 0 T1007 T1018
theorem T1006_ok : Node.check D_R22222 T1006 [((489/512),(163/128)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1007_ok T1018_ok
def T1005 : Node := Node.leaf L1005
theorem T1005_ok : Node.check D_R22222 T1005 [((489/512),(163/128)),((6075/2048),(405/128)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1005_ok
def T1004 : Node := Node.split 2 T1005 T1006
theorem T1004_ok : Node.check D_R22222 T1004 [((489/512),(163/128)),((6075/2048),(405/128)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1005_ok T1006_ok
def T1003 : Node := Node.leaf L1003
theorem T1003_ok : Node.check D_R22222 T1003 [((1141/1024),(163/128)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L1003_ok
def T1002 : Node := Node.leaf L1002
theorem T1002_ok : Node.check D_R22222 T1002 [((489/512),(1141/1024)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L1002_ok
def T1001 : Node := Node.leaf L1001
theorem T1001_ok : Node.check D_R22222 T1001 [((489/512),(1141/1024)),((11745/4096),(6075/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1001_ok
def T1000 : Node := Node.leaf L1000
theorem T1000_ok : Node.check D_R22222 T1000 [((489/512),(1141/1024)),((2835/1024),(11745/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L1000_ok
def T999 : Node := Node.split 1 T1000 T1001
theorem T999_ok : Node.check D_R22222 T999 [((489/512),(1141/1024)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1000_ok T1001_ok
def T998 : Node := Node.split 3 T999 T1002
theorem T998_ok : Node.check D_R22222 T998 [((489/512),(1141/1024)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T999_ok T1002_ok
def T997 : Node := Node.split 0 T998 T1003
theorem T997_ok : Node.check D_R22222 T997 [((489/512),(163/128)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T998_ok T1003_ok
def T996 : Node := Node.leaf L996
theorem T996_ok : Node.check D_R22222 T996 [((489/512),(163/128)),((2835/1024),(6075/2048)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L996_ok
def T995 : Node := Node.split 2 T996 T997
theorem T995_ok : Node.check D_R22222 T995 [((489/512),(163/128)),((2835/1024),(6075/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T996_ok T997_ok
def T994 : Node := Node.split 1 T995 T1004
theorem T994_ok : Node.check D_R22222 T994 [((489/512),(163/128)),((2835/1024),(405/128)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T995_ok T1004_ok
def T993 : Node := Node.split 3 T994 T1019
theorem T993_ok : Node.check D_R22222 T993 [((489/512),(163/128)),((2835/1024),(405/128)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T994_ok T1019_ok
def T992 : Node := Node.leaf L992
theorem T992_ok : Node.check D_R22222 T992 [((163/256),(489/512)),((2835/1024),(405/128)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L992_ok
def T991 : Node := Node.split 0 T992 T993
theorem T991_ok : Node.check D_R22222 T991 [((163/256),(163/128)),((2835/1024),(405/128)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T992_ok T993_ok
def T990 : Node := Node.split 2 T991 T1020
theorem T990_ok : Node.check D_R22222 T990 [((163/256),(163/128)),((2835/1024),(405/128)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T991_ok T1020_ok
def T989 : Node := Node.leaf L989
theorem T989_ok : Node.check D_R22222 T989 [((163/256),(163/128)),((1215/512),(2835/1024)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L989_ok
def T988 : Node := Node.split 1 T989 T990
theorem T988_ok : Node.check D_R22222 T988 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T989_ok T990_ok
def T987 : Node := Node.leaf L987
theorem T987_ok : Node.check D_R22222 T987 [((163/256),(163/128)),((2835/1024),(405/128)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L987_ok
def T986 : Node := Node.leaf L986
theorem T986_ok : Node.check D_R22222 T986 [((163/256),(163/128)),((1215/512),(2835/1024)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L986_ok
def T985 : Node := Node.split 1 T986 T987
theorem T985_ok : Node.check D_R22222 T985 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T986_ok T987_ok
def T984 : Node := Node.split 3 T985 T988
theorem T984_ok : Node.check D_R22222 T984 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T985_ok T988_ok
def T983 : Node := Node.leaf L983
theorem T983_ok : Node.check D_R22222 T983 [((0),(163/256)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L983_ok
def T982 : Node := Node.split 0 T983 T984
theorem T982_ok : Node.check D_R22222 T982 [((0),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T983_ok T984_ok
def T981 : Node := Node.leaf L981
theorem T981_ok : Node.check D_R22222 T981 [((0),(163/128)),((1215/512),(405/128)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L981_ok
def T980 : Node := Node.split 2 T981 T982
theorem T980_ok : Node.check D_R22222 T980 [((0),(163/128)),((1215/512),(405/128)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T981_ok T982_ok
def T979 : Node := Node.leaf L979
theorem T979_ok : Node.check D_R22222 T979 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L979_ok
def T978 : Node := Node.leaf L978
theorem T978_ok : Node.check D_R22222 T978 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L978_ok
def T977 : Node := Node.leaf L977
theorem T977_ok : Node.check D_R22222 T977 [((489/512),(163/128)),((4455/2048),(1215/512)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L977_ok
def T976 : Node := Node.leaf L976
theorem T976_ok : Node.check D_R22222 T976 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L976_ok
def T975 : Node := Node.leaf L975
theorem T975_ok : Node.check D_R22222 T975 [((1141/1024),(163/128)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L975_ok
def T974 : Node := Node.leaf L974
theorem T974_ok : Node.check D_R22222 T974 [((1141/1024),(163/128)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L974_ok
def T973 : Node := Node.leaf L973
theorem T973_ok : Node.check D_R22222 T973 [((1141/1024),(163/128)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L973_ok
def T972 : Node := Node.split 2 T973 T974
theorem T972_ok : Node.check D_R22222 T972 [((1141/1024),(163/128)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T973_ok T974_ok
def T971 : Node := Node.split 1 T972 T975
theorem T971_ok : Node.check D_R22222 T971 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T972_ok T975_ok
def T970 : Node := Node.split 3 T971 T976
theorem T970_ok : Node.check D_R22222 T970 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T971_ok T976_ok
def T969 : Node := Node.leaf L969
theorem T969_ok : Node.check D_R22222 T969 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L969_ok
def T968 : Node := Node.leaf L968
theorem T968_ok : Node.check D_R22222 T968 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L968_ok
def T967 : Node := Node.leaf L967
theorem T967_ok : Node.check D_R22222 T967 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((4401/2048),(1141/512))] = true := Node.check_leaf_of _ _ _ L967_ok
def T966 : Node := Node.leaf L966
theorem T966_ok : Node.check D_R22222 T966 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((2119/1024),(4401/2048))] = true := Node.check_leaf_of _ _ _ L966_ok
def T965 : Node := Node.split 3 T966 T967
theorem T965_ok : Node.check D_R22222 T965 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T966_ok T967_ok
def T964 : Node := Node.leaf L964
theorem T964_ok : Node.check D_R22222 T964 [((489/512),(2119/2048)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L964_ok
def T963 : Node := Node.split 0 T964 T965
theorem T963_ok : Node.check D_R22222 T963 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T964_ok T965_ok
def T962 : Node := Node.split 2 T963 T968
theorem T962_ok : Node.check D_R22222 T962 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T963_ok T968_ok
def T961 : Node := Node.split 1 T962 T969
theorem T961_ok : Node.check D_R22222 T961 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T962_ok T969_ok
def T960 : Node := Node.leaf L960
theorem T960_ok : Node.check D_R22222 T960 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L960_ok
def T959 : Node := Node.leaf L959
theorem T959_ok : Node.check D_R22222 T959 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L959_ok
def T958 : Node := Node.split 2 T959 T960
theorem T958_ok : Node.check D_R22222 T958 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T959_ok T960_ok
def T957 : Node := Node.leaf L957
theorem T957_ok : Node.check D_R22222 T957 [((2119/2048),(1141/1024)),((16605/8192),(8505/4096)),((4455/4096),(1215/1024)),((4075/2048),(2119/1024))] = true := Node.check_leaf_of _ _ _ L957_ok
def T956 : Node := Node.leaf L956
theorem T956_ok : Node.check D_R22222 T956 [((2119/2048),(1141/1024)),((2025/1024),(16605/8192)),((4455/4096),(1215/1024)),((4075/2048),(2119/1024))] = true := Node.check_leaf_of _ _ _ L956_ok
def T955 : Node := Node.split 1 T956 T957
theorem T955_ok : Node.check D_R22222 T955 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((4075/2048),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T956_ok T957_ok
def T954 : Node := Node.leaf L954
theorem T954_ok : Node.check D_R22222 T954 [((2119/2048),(1141/1024)),((16605/8192),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(4075/2048))] = true := Node.check_leaf_of _ _ _ L954_ok
def T953 : Node := Node.leaf L953
theorem T953_ok : Node.check D_R22222 T953 [((2119/2048),(1141/1024)),((2025/1024),(16605/8192)),((4455/4096),(1215/1024)),((489/256),(4075/2048))] = true := Node.check_leaf_of _ _ _ L953_ok
def T952 : Node := Node.split 1 T953 T954
theorem T952_ok : Node.check D_R22222 T952 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(4075/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T953_ok T954_ok
def T951 : Node := Node.split 3 T952 T955
theorem T951_ok : Node.check D_R22222 T951 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T952_ok T955_ok
def T950 : Node := Node.leaf L950
theorem T950_ok : Node.check D_R22222 T950 [((489/512),(2119/2048)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L950_ok
def T949 : Node := Node.split 0 T950 T951
theorem T949_ok : Node.check D_R22222 T949 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T950_ok T951_ok
def T948 : Node := Node.leaf L948
theorem T948_ok : Node.check D_R22222 T948 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L948_ok
def T947 : Node := Node.split 2 T948 T949
theorem T947_ok : Node.check D_R22222 T947 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T948_ok T949_ok
def T946 : Node := Node.split 1 T947 T958
theorem T946_ok : Node.check D_R22222 T946 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T947_ok T958_ok
def T945 : Node := Node.split 3 T946 T961
theorem T945_ok : Node.check D_R22222 T945 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T946_ok T961_ok
def T944 : Node := Node.split 0 T945 T970
theorem T944_ok : Node.check D_R22222 T944 [((489/512),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T945_ok T970_ok
def T943 : Node := Node.leaf L943
theorem T943_ok : Node.check D_R22222 T943 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L943_ok
def T942 : Node := Node.split 2 T943 T944
theorem T942_ok : Node.check D_R22222 T942 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T943_ok T944_ok
def T941 : Node := Node.split 1 T942 T977
theorem T941_ok : Node.check D_R22222 T941 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T942_ok T977_ok
def T940 : Node := Node.split 3 T941 T978
theorem T940_ok : Node.check D_R22222 T940 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T941_ok T978_ok
def T939 : Node := Node.leaf L939
theorem T939_ok : Node.check D_R22222 T939 [((163/256),(489/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L939_ok
def T938 : Node := Node.split 0 T939 T940
theorem T938_ok : Node.check D_R22222 T938 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T939_ok T940_ok
def T937 : Node := Node.split 2 T938 T979
theorem T937_ok : Node.check D_R22222 T937 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T938_ok T979_ok
def T936 : Node := Node.leaf L936
theorem T936_ok : Node.check D_R22222 T936 [((163/256),(163/128)),((405/256),(2025/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L936_ok
def T935 : Node := Node.leaf L935
theorem T935_ok : Node.check D_R22222 T935 [((489/512),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L935_ok
def T934 : Node := Node.leaf L934
theorem T934_ok : Node.check D_R22222 T934 [((1141/1024),(163/128)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L934_ok
def T933 : Node := Node.leaf L933
theorem T933_ok : Node.check D_R22222 T933 [((1141/1024),(163/128)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L933_ok
def T932 : Node := Node.split 1 T933 T934
theorem T932_ok : Node.check D_R22222 T932 [((1141/1024),(163/128)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T933_ok T934_ok
def T931 : Node := Node.leaf L931
theorem T931_ok : Node.check D_R22222 T931 [((1141/1024),(163/128)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L931_ok
def T930 : Node := Node.leaf L930
theorem T930_ok : Node.check D_R22222 T930 [((1141/1024),(163/128)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L930_ok
def T929 : Node := Node.split 2 T930 T931
theorem T929_ok : Node.check D_R22222 T929 [((1141/1024),(163/128)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T930_ok T931_ok
def T928 : Node := Node.leaf L928
theorem T928_ok : Node.check D_R22222 T928 [((1141/1024),(163/128)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L928_ok
def T927 : Node := Node.split 1 T928 T929
theorem T927_ok : Node.check D_R22222 T927 [((1141/1024),(163/128)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T928_ok T929_ok
def T926 : Node := Node.split 3 T927 T932
theorem T926_ok : Node.check D_R22222 T926 [((1141/1024),(163/128)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T927_ok T932_ok
def T925 : Node := Node.leaf L925
theorem T925_ok : Node.check D_R22222 T925 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L925_ok
def T924 : Node := Node.leaf L924
theorem T924_ok : Node.check D_R22222 T924 [((2119/2048),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((4401/2048),(1141/512))] = true := Node.check_leaf_of _ _ _ L924_ok
def T923 : Node := Node.leaf L923
theorem T923_ok : Node.check D_R22222 T923 [((2119/2048),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((2119/1024),(4401/2048))] = true := Node.check_leaf_of _ _ _ L923_ok
def T922 : Node := Node.split 3 T923 T924
theorem T922_ok : Node.check D_R22222 T922 [((2119/2048),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T923_ok T924_ok
def T921 : Node := Node.leaf L921
theorem T921_ok : Node.check D_R22222 T921 [((489/512),(2119/2048)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L921_ok
def T920 : Node := Node.split 0 T921 T922
theorem T920_ok : Node.check D_R22222 T920 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T921_ok T922_ok
def T919 : Node := Node.split 2 T920 T925
theorem T919_ok : Node.check D_R22222 T919 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T920_ok T925_ok
def T918 : Node := Node.leaf L918
theorem T918_ok : Node.check D_R22222 T918 [((489/512),(1141/1024)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L918_ok
def T917 : Node := Node.split 1 T918 T919
theorem T917_ok : Node.check D_R22222 T917 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T918_ok T919_ok
def T916 : Node := Node.leaf L916
theorem T916_ok : Node.check D_R22222 T916 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L916_ok
def T915 : Node := Node.leaf L915
theorem T915_ok : Node.check D_R22222 T915 [((489/512),(1141/1024)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L915_ok
def T914 : Node := Node.split 1 T915 T916
theorem T914_ok : Node.check D_R22222 T914 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T915_ok T916_ok
def T913 : Node := Node.split 3 T914 T917
theorem T913_ok : Node.check D_R22222 T913 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T914_ok T917_ok
def T912 : Node := Node.split 0 T913 T926
theorem T912_ok : Node.check D_R22222 T912 [((489/512),(163/128)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T913_ok T926_ok
def T911 : Node := Node.leaf L911
theorem T911_ok : Node.check D_R22222 T911 [((489/512),(163/128)),((3645/2048),(2025/1024)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L911_ok
def T910 : Node := Node.split 2 T911 T912
theorem T910_ok : Node.check D_R22222 T910 [((489/512),(163/128)),((3645/2048),(2025/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T911_ok T912_ok
def T909 : Node := Node.leaf L909
theorem T909_ok : Node.check D_R22222 T909 [((489/512),(163/128)),((405/256),(3645/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L909_ok
def T908 : Node := Node.split 1 T909 T910
theorem T908_ok : Node.check D_R22222 T908 [((489/512),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T909_ok T910_ok
def T907 : Node := Node.split 3 T908 T935
theorem T907_ok : Node.check D_R22222 T907 [((489/512),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T908_ok T935_ok
def T906 : Node := Node.leaf L906
theorem T906_ok : Node.check D_R22222 T906 [((163/256),(489/512)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L906_ok
def T905 : Node := Node.split 0 T906 T907
theorem T905_ok : Node.check D_R22222 T905 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T906_ok T907_ok
def T904 : Node := Node.split 2 T905 T936
theorem T904_ok : Node.check D_R22222 T904 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T905_ok T936_ok
def T903 : Node := Node.split 1 T904 T937
theorem T903_ok : Node.check D_R22222 T903 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T904_ok T937_ok
def T902 : Node := Node.leaf L902
theorem T902_ok : Node.check D_R22222 T902 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L902_ok
def T901 : Node := Node.leaf L901
theorem T901_ok : Node.check D_R22222 T901 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((815/512),(489/256))] = true := Node.check_leaf_of _ _ _ L901_ok
def T900 : Node := Node.leaf L900
theorem T900_ok : Node.check D_R22222 T900 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/128),(815/512))] = true := Node.check_leaf_of _ _ _ L900_ok
def T899 : Node := Node.split 3 T900 T901
theorem T899_ok : Node.check D_R22222 T899 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T900_ok T901_ok
def T898 : Node := Node.leaf L898
theorem T898_ok : Node.check D_R22222 T898 [((163/256),(489/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L898_ok
def T897 : Node := Node.split 0 T898 T899
theorem T897_ok : Node.check D_R22222 T897 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T898_ok T899_ok
def T896 : Node := Node.split 2 T897 T902
theorem T896_ok : Node.check D_R22222 T896 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T897_ok T902_ok
def T895 : Node := Node.leaf L895
theorem T895_ok : Node.check D_R22222 T895 [((163/256),(163/128)),((405/256),(2025/1024)),((1215/1024),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L895_ok
def T894 : Node := Node.leaf L894
theorem T894_ok : Node.check D_R22222 T894 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L894_ok
def T893 : Node := Node.split 2 T894 T895
theorem T893_ok : Node.check D_R22222 T893 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T894_ok T895_ok
def T892 : Node := Node.split 1 T893 T896
theorem T892_ok : Node.check D_R22222 T892 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T893_ok T896_ok
def T891 : Node := Node.split 3 T892 T903
theorem T891_ok : Node.check D_R22222 T891 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T892_ok T903_ok
def T890 : Node := Node.leaf L890
theorem T890_ok : Node.check D_R22222 T890 [((0),(163/256)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L890_ok
def T889 : Node := Node.split 0 T890 T891
theorem T889_ok : Node.check D_R22222 T889 [((0),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T890_ok T891_ok
def T888 : Node := Node.leaf L888
theorem T888_ok : Node.check D_R22222 T888 [((0),(163/128)),((405/256),(1215/512)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L888_ok
def T887 : Node := Node.split 2 T888 T889
theorem T887_ok : Node.check D_R22222 T887 [((0),(163/128)),((405/256),(1215/512)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T888_ok T889_ok
def T886 : Node := Node.split 1 T887 T980
theorem T886_ok : Node.check D_R22222 T886 [((0),(163/128)),((405/256),(405/128)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T887_ok T980_ok
def T885 : Node := Node.leaf L885
theorem T885_ok : Node.check D_R22222 T885 [((163/256),(163/128)),((2835/1024),(405/128)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L885_ok
def T884 : Node := Node.leaf L884
theorem T884_ok : Node.check D_R22222 T884 [((1141/1024),(163/128)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L884_ok
def T883 : Node := Node.leaf L883
theorem T883_ok : Node.check D_R22222 T883 [((1141/1024),(163/128)),((12555/4096),(405/128)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L883_ok
def T882 : Node := Node.leaf L882
theorem T882_ok : Node.check D_R22222 T882 [((1141/1024),(163/128)),((6075/2048),(12555/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L882_ok
def T881 : Node := Node.leaf L881
theorem T881_ok : Node.check D_R22222 T881 [((1141/1024),(163/128)),((6075/2048),(12555/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L881_ok
def T880 : Node := Node.split 2 T881 T882
theorem T880_ok : Node.check D_R22222 T880 [((1141/1024),(163/128)),((6075/2048),(12555/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T881_ok T882_ok
def T879 : Node := Node.split 1 T880 T883
theorem T879_ok : Node.check D_R22222 T879 [((1141/1024),(163/128)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T880_ok T883_ok
def T878 : Node := Node.split 3 T879 T884
theorem T878_ok : Node.check D_R22222 T878 [((1141/1024),(163/128)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T879_ok T884_ok
def T877 : Node := Node.leaf L877
theorem T877_ok : Node.check D_R22222 T877 [((489/512),(1141/1024)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L877_ok
def T876 : Node := Node.leaf L876
theorem T876_ok : Node.check D_R22222 T876 [((489/512),(1141/1024)),((12555/4096),(405/128)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L876_ok
def T875 : Node := Node.leaf L875
theorem T875_ok : Node.check D_R22222 T875 [((489/512),(1141/1024)),((12555/4096),(405/128)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L875_ok
def T874 : Node := Node.split 2 T875 T876
theorem T874_ok : Node.check D_R22222 T874 [((489/512),(1141/1024)),((12555/4096),(405/128)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T875_ok T876_ok
def T873 : Node := Node.leaf L873
theorem T873_ok : Node.check D_R22222 T873 [((2119/2048),(1141/1024)),((6075/2048),(12555/4096)),((4455/4096),(1215/1024)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L873_ok
def T872 : Node := Node.leaf L872
theorem T872_ok : Node.check D_R22222 T872 [((2119/2048),(1141/1024)),((6075/2048),(12555/4096)),((4455/4096),(1215/1024)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L872_ok
def T871 : Node := Node.split 3 T872 T873
theorem T871_ok : Node.check D_R22222 T871 [((2119/2048),(1141/1024)),((6075/2048),(12555/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T872_ok T873_ok
def T870 : Node := Node.leaf L870
theorem T870_ok : Node.check D_R22222 T870 [((489/512),(2119/2048)),((6075/2048),(12555/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L870_ok
def T869 : Node := Node.split 0 T870 T871
theorem T869_ok : Node.check D_R22222 T869 [((489/512),(1141/1024)),((6075/2048),(12555/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T870_ok T871_ok
def T868 : Node := Node.leaf L868
theorem T868_ok : Node.check D_R22222 T868 [((489/512),(1141/1024)),((6075/2048),(12555/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L868_ok
def T867 : Node := Node.split 2 T868 T869
theorem T867_ok : Node.check D_R22222 T867 [((489/512),(1141/1024)),((6075/2048),(12555/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T868_ok T869_ok
def T866 : Node := Node.split 1 T867 T874
theorem T866_ok : Node.check D_R22222 T866 [((489/512),(1141/1024)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T867_ok T874_ok
def T865 : Node := Node.split 3 T866 T877
theorem T865_ok : Node.check D_R22222 T865 [((489/512),(1141/1024)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T866_ok T877_ok
def T864 : Node := Node.split 0 T865 T878
theorem T864_ok : Node.check D_R22222 T864 [((489/512),(163/128)),((6075/2048),(405/128)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T865_ok T878_ok
def T863 : Node := Node.leaf L863
theorem T863_ok : Node.check D_R22222 T863 [((489/512),(163/128)),((6075/2048),(405/128)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L863_ok
def T862 : Node := Node.split 2 T863 T864
theorem T862_ok : Node.check D_R22222 T862 [((489/512),(163/128)),((6075/2048),(405/128)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T863_ok T864_ok
def T861 : Node := Node.leaf L861
theorem T861_ok : Node.check D_R22222 T861 [((1141/1024),(163/128)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L861_ok
def T860 : Node := Node.leaf L860
theorem T860_ok : Node.check D_R22222 T860 [((1141/1024),(163/128)),((11745/4096),(6075/2048)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L860_ok
def T859 : Node := Node.leaf L859
theorem T859_ok : Node.check D_R22222 T859 [((1141/1024),(163/128)),((11745/4096),(6075/2048)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L859_ok
def T858 : Node := Node.split 2 T859 T860
theorem T858_ok : Node.check D_R22222 T858 [((1141/1024),(163/128)),((11745/4096),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T859_ok T860_ok
def T857 : Node := Node.leaf L857
theorem T857_ok : Node.check D_R22222 T857 [((1141/1024),(163/128)),((2835/1024),(11745/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L857_ok
def T856 : Node := Node.split 1 T857 T858
theorem T856_ok : Node.check D_R22222 T856 [((1141/1024),(163/128)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T857_ok T858_ok
def T855 : Node := Node.split 3 T856 T861
theorem T855_ok : Node.check D_R22222 T855 [((1141/1024),(163/128)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T856_ok T861_ok
def T854 : Node := Node.leaf L854
theorem T854_ok : Node.check D_R22222 T854 [((489/512),(1141/1024)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L854_ok
def T853 : Node := Node.leaf L853
theorem T853_ok : Node.check D_R22222 T853 [((2119/2048),(1141/1024)),((11745/4096),(6075/2048)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L853_ok
def T852 : Node := Node.leaf L852
theorem T852_ok : Node.check D_R22222 T852 [((489/512),(2119/2048)),((11745/4096),(6075/2048)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L852_ok
def T851 : Node := Node.split 0 T852 T853
theorem T851_ok : Node.check D_R22222 T851 [((489/512),(1141/1024)),((11745/4096),(6075/2048)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T852_ok T853_ok
def T850 : Node := Node.leaf L850
theorem T850_ok : Node.check D_R22222 T850 [((489/512),(1141/1024)),((11745/4096),(6075/2048)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L850_ok
def T849 : Node := Node.split 2 T850 T851
theorem T849_ok : Node.check D_R22222 T849 [((489/512),(1141/1024)),((11745/4096),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T850_ok T851_ok
def T848 : Node := Node.leaf L848
theorem T848_ok : Node.check D_R22222 T848 [((489/512),(1141/1024)),((2835/1024),(11745/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L848_ok
def T847 : Node := Node.split 1 T848 T849
theorem T847_ok : Node.check D_R22222 T847 [((489/512),(1141/1024)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T848_ok T849_ok
def T846 : Node := Node.split 3 T847 T854
theorem T846_ok : Node.check D_R22222 T846 [((489/512),(1141/1024)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T847_ok T854_ok
def T845 : Node := Node.split 0 T846 T855
theorem T845_ok : Node.check D_R22222 T845 [((489/512),(163/128)),((2835/1024),(6075/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T846_ok T855_ok
def T844 : Node := Node.leaf L844
theorem T844_ok : Node.check D_R22222 T844 [((489/512),(163/128)),((2835/1024),(6075/2048)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L844_ok
def T843 : Node := Node.split 2 T844 T845
theorem T843_ok : Node.check D_R22222 T843 [((489/512),(163/128)),((2835/1024),(6075/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T844_ok T845_ok
def T842 : Node := Node.split 1 T843 T862
theorem T842_ok : Node.check D_R22222 T842 [((489/512),(163/128)),((2835/1024),(405/128)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T843_ok T862_ok
def T841 : Node := Node.leaf L841
theorem T841_ok : Node.check D_R22222 T841 [((489/512),(163/128)),((2835/1024),(405/128)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L841_ok
def T840 : Node := Node.split 3 T841 T842
theorem T840_ok : Node.check D_R22222 T840 [((489/512),(163/128)),((2835/1024),(405/128)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T841_ok T842_ok
def T839 : Node := Node.leaf L839
theorem T839_ok : Node.check D_R22222 T839 [((163/256),(489/512)),((2835/1024),(405/128)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L839_ok
def T838 : Node := Node.split 0 T839 T840
theorem T838_ok : Node.check D_R22222 T838 [((163/256),(163/128)),((2835/1024),(405/128)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T839_ok T840_ok
def T837 : Node := Node.split 2 T838 T885
theorem T837_ok : Node.check D_R22222 T837 [((163/256),(163/128)),((2835/1024),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T838_ok T885_ok
def T836 : Node := Node.leaf L836
theorem T836_ok : Node.check D_R22222 T836 [((163/256),(163/128)),((1215/512),(2835/1024)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L836_ok
def T835 : Node := Node.split 1 T836 T837
theorem T835_ok : Node.check D_R22222 T835 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T836_ok T837_ok
def T834 : Node := Node.leaf L834
theorem T834_ok : Node.check D_R22222 T834 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L834_ok
def T833 : Node := Node.split 3 T834 T835
theorem T833_ok : Node.check D_R22222 T833 [((163/256),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T834_ok T835_ok
def T832 : Node := Node.leaf L832
theorem T832_ok : Node.check D_R22222 T832 [((0),(163/256)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L832_ok
def T831 : Node := Node.split 0 T832 T833
theorem T831_ok : Node.check D_R22222 T831 [((0),(163/128)),((1215/512),(405/128)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T832_ok T833_ok
def T830 : Node := Node.leaf L830
theorem T830_ok : Node.check D_R22222 T830 [((0),(163/128)),((1215/512),(405/128)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L830_ok
def T829 : Node := Node.split 2 T830 T831
theorem T829_ok : Node.check D_R22222 T829 [((0),(163/128)),((1215/512),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T830_ok T831_ok
def T828 : Node := Node.leaf L828
theorem T828_ok : Node.check D_R22222 T828 [((163/256),(163/128)),((2025/1024),(1215/512)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L828_ok
def T827 : Node := Node.leaf L827
theorem T827_ok : Node.check D_R22222 T827 [((489/512),(163/128)),((4455/2048),(1215/512)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L827_ok
def T826 : Node := Node.leaf L826
theorem T826_ok : Node.check D_R22222 T826 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L826_ok
def T825 : Node := Node.leaf L825
theorem T825_ok : Node.check D_R22222 T825 [((1141/1024),(163/128)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L825_ok
def T824 : Node := Node.leaf L824
theorem T824_ok : Node.check D_R22222 T824 [((1141/1024),(163/128)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L824_ok
def T823 : Node := Node.leaf L823
theorem T823_ok : Node.check D_R22222 T823 [((2445/2048),(163/128)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L823_ok
def T822 : Node := Node.leaf L822
theorem T822_ok : Node.check D_R22222 T822 [((1141/1024),(2445/2048)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L822_ok
def T821 : Node := Node.split 0 T822 T823
theorem T821_ok : Node.check D_R22222 T821 [((1141/1024),(163/128)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T822_ok T823_ok
def T820 : Node := Node.split 2 T821 T824
theorem T820_ok : Node.check D_R22222 T820 [((1141/1024),(163/128)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T821_ok T824_ok
def T819 : Node := Node.split 1 T820 T825
theorem T819_ok : Node.check D_R22222 T819 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T820_ok T825_ok
def T818 : Node := Node.split 3 T819 T826
theorem T818_ok : Node.check D_R22222 T818 [((1141/1024),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T819_ok T826_ok
def T817 : Node := Node.leaf L817
theorem T817_ok : Node.check D_R22222 T817 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L817_ok
def T816 : Node := Node.leaf L816
theorem T816_ok : Node.check D_R22222 T816 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L816_ok
def T815 : Node := Node.leaf L815
theorem T815_ok : Node.check D_R22222 T815 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L815_ok
def T814 : Node := Node.leaf L814
theorem T814_ok : Node.check D_R22222 T814 [((489/512),(2119/2048)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L814_ok
def T813 : Node := Node.split 0 T814 T815
theorem T813_ok : Node.check D_R22222 T813 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T814_ok T815_ok
def T812 : Node := Node.split 2 T813 T816
theorem T812_ok : Node.check D_R22222 T812 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T813_ok T816_ok
def T811 : Node := Node.split 1 T812 T817
theorem T811_ok : Node.check D_R22222 T811 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T812_ok T817_ok
def T810 : Node := Node.leaf L810
theorem T810_ok : Node.check D_R22222 T810 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L810_ok
def T809 : Node := Node.leaf L809
theorem T809_ok : Node.check D_R22222 T809 [((2119/2048),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L809_ok
def T808 : Node := Node.leaf L808
theorem T808_ok : Node.check D_R22222 T808 [((489/512),(2119/2048)),((8505/4096),(4455/2048)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L808_ok
def T807 : Node := Node.split 0 T808 T809
theorem T807_ok : Node.check D_R22222 T807 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T808_ok T809_ok
def T806 : Node := Node.split 2 T807 T810
theorem T806_ok : Node.check D_R22222 T806 [((489/512),(1141/1024)),((8505/4096),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T807_ok T810_ok
def T805 : Node := Node.leaf L805
theorem T805_ok : Node.check D_R22222 T805 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L805_ok
def T804 : Node := Node.leaf L804
theorem T804_ok : Node.check D_R22222 T804 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L804_ok
def T803 : Node := Node.split 3 T804 T805
theorem T803_ok : Node.check D_R22222 T803 [((2119/2048),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T804_ok T805_ok
def T802 : Node := Node.leaf L802
theorem T802_ok : Node.check D_R22222 T802 [((489/512),(2119/2048)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L802_ok
def T801 : Node := Node.leaf L801
theorem T801_ok : Node.check D_R22222 T801 [((489/512),(2119/2048)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L801_ok
def T800 : Node := Node.split 3 T801 T802
theorem T800_ok : Node.check D_R22222 T800 [((489/512),(2119/2048)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T801_ok T802_ok
def T799 : Node := Node.split 0 T800 T803
theorem T799_ok : Node.check D_R22222 T799 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T800_ok T803_ok
def T798 : Node := Node.leaf L798
theorem T798_ok : Node.check D_R22222 T798 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L798_ok
def T797 : Node := Node.split 2 T798 T799
theorem T797_ok : Node.check D_R22222 T797 [((489/512),(1141/1024)),((2025/1024),(8505/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T798_ok T799_ok
def T796 : Node := Node.split 1 T797 T806
theorem T796_ok : Node.check D_R22222 T796 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T797_ok T806_ok
def T795 : Node := Node.split 3 T796 T811
theorem T795_ok : Node.check D_R22222 T795 [((489/512),(1141/1024)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T796_ok T811_ok
def T794 : Node := Node.split 0 T795 T818
theorem T794_ok : Node.check D_R22222 T794 [((489/512),(163/128)),((2025/1024),(4455/2048)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T795_ok T818_ok
def T793 : Node := Node.leaf L793
theorem T793_ok : Node.check D_R22222 T793 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L793_ok
def T792 : Node := Node.split 2 T793 T794
theorem T792_ok : Node.check D_R22222 T792 [((489/512),(163/128)),((2025/1024),(4455/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T793_ok T794_ok
def T791 : Node := Node.split 1 T792 T827
theorem T791_ok : Node.check D_R22222 T791 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T792_ok T827_ok
def T790 : Node := Node.leaf L790
theorem T790_ok : Node.check D_R22222 T790 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L790_ok
def T789 : Node := Node.split 3 T790 T791
theorem T789_ok : Node.check D_R22222 T789 [((489/512),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T790_ok T791_ok
def T788 : Node := Node.leaf L788
theorem T788_ok : Node.check D_R22222 T788 [((163/256),(489/512)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L788_ok
def T787 : Node := Node.split 0 T788 T789
theorem T787_ok : Node.check D_R22222 T787 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T788_ok T789_ok
def T786 : Node := Node.split 2 T787 T828
theorem T786_ok : Node.check D_R22222 T786 [((163/256),(163/128)),((2025/1024),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T787_ok T828_ok
def T785 : Node := Node.leaf L785
theorem T785_ok : Node.check D_R22222 T785 [((163/256),(163/128)),((405/256),(2025/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L785_ok
def T784 : Node := Node.leaf L784
theorem T784_ok : Node.check D_R22222 T784 [((1141/1024),(163/128)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L784_ok
def T783 : Node := Node.leaf L783
theorem T783_ok : Node.check D_R22222 T783 [((1141/1024),(163/128)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L783_ok
def T782 : Node := Node.leaf L782
theorem T782_ok : Node.check D_R22222 T782 [((1141/1024),(163/128)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L782_ok
def T781 : Node := Node.split 2 T782 T783
theorem T781_ok : Node.check D_R22222 T781 [((1141/1024),(163/128)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T782_ok T783_ok
def T780 : Node := Node.leaf L780
theorem T780_ok : Node.check D_R22222 T780 [((1141/1024),(163/128)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L780_ok
def T779 : Node := Node.split 1 T780 T781
theorem T779_ok : Node.check D_R22222 T779 [((1141/1024),(163/128)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T780_ok T781_ok
def T778 : Node := Node.split 3 T779 T784
theorem T778_ok : Node.check D_R22222 T778 [((1141/1024),(163/128)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T779_ok T784_ok
def T777 : Node := Node.leaf L777
theorem T777_ok : Node.check D_R22222 T777 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L777_ok
def T776 : Node := Node.leaf L776
theorem T776_ok : Node.check D_R22222 T776 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L776_ok
def T775 : Node := Node.split 2 T776 T777
theorem T775_ok : Node.check D_R22222 T775 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T776_ok T777_ok
def T774 : Node := Node.leaf L774
theorem T774_ok : Node.check D_R22222 T774 [((489/512),(1141/1024)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L774_ok
def T773 : Node := Node.split 1 T774 T775
theorem T773_ok : Node.check D_R22222 T773 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T774_ok T775_ok
def T772 : Node := Node.leaf L772
theorem T772_ok : Node.check D_R22222 T772 [((2119/2048),(1141/1024)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L772_ok
def T771 : Node := Node.leaf L771
theorem T771_ok : Node.check D_R22222 T771 [((2119/2048),(1141/1024)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L771_ok
def T770 : Node := Node.split 3 T771 T772
theorem T770_ok : Node.check D_R22222 T770 [((2119/2048),(1141/1024)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T771_ok T772_ok
def T769 : Node := Node.leaf L769
theorem T769_ok : Node.check D_R22222 T769 [((489/512),(2119/2048)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L769_ok
def T768 : Node := Node.split 0 T769 T770
theorem T768_ok : Node.check D_R22222 T768 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T769_ok T770_ok
def T767 : Node := Node.leaf L767
theorem T767_ok : Node.check D_R22222 T767 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L767_ok
def T766 : Node := Node.split 2 T767 T768
theorem T766_ok : Node.check D_R22222 T766 [((489/512),(1141/1024)),((7695/4096),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T767_ok T768_ok
def T765 : Node := Node.leaf L765
theorem T765_ok : Node.check D_R22222 T765 [((489/512),(1141/1024)),((3645/2048),(7695/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L765_ok
def T764 : Node := Node.split 1 T765 T766
theorem T764_ok : Node.check D_R22222 T764 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T765_ok T766_ok
def T763 : Node := Node.split 3 T764 T773
theorem T763_ok : Node.check D_R22222 T763 [((489/512),(1141/1024)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T764_ok T773_ok
def T762 : Node := Node.split 0 T763 T778
theorem T762_ok : Node.check D_R22222 T762 [((489/512),(163/128)),((3645/2048),(2025/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T763_ok T778_ok
def T761 : Node := Node.leaf L761
theorem T761_ok : Node.check D_R22222 T761 [((489/512),(163/128)),((3645/2048),(2025/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L761_ok
def T760 : Node := Node.split 2 T761 T762
theorem T760_ok : Node.check D_R22222 T760 [((489/512),(163/128)),((3645/2048),(2025/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T761_ok T762_ok
def T759 : Node := Node.leaf L759
theorem T759_ok : Node.check D_R22222 T759 [((489/512),(163/128)),((405/256),(3645/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L759_ok
def T758 : Node := Node.split 1 T759 T760
theorem T758_ok : Node.check D_R22222 T758 [((489/512),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T759_ok T760_ok
def T757 : Node := Node.leaf L757
theorem T757_ok : Node.check D_R22222 T757 [((489/512),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L757_ok
def T756 : Node := Node.split 3 T757 T758
theorem T756_ok : Node.check D_R22222 T756 [((489/512),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T757_ok T758_ok
def T755 : Node := Node.leaf L755
theorem T755_ok : Node.check D_R22222 T755 [((163/256),(489/512)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L755_ok
def T754 : Node := Node.split 0 T755 T756
theorem T754_ok : Node.check D_R22222 T754 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T755_ok T756_ok
def T753 : Node := Node.split 2 T754 T785
theorem T753_ok : Node.check D_R22222 T753 [((163/256),(163/128)),((405/256),(2025/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T754_ok T785_ok
def T752 : Node := Node.split 1 T753 T786
theorem T752_ok : Node.check D_R22222 T752 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T753_ok T786_ok
def T751 : Node := Node.leaf L751
theorem T751_ok : Node.check D_R22222 T751 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L751_ok
def T750 : Node := Node.split 3 T751 T752
theorem T750_ok : Node.check D_R22222 T750 [((163/256),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T751_ok T752_ok
def T749 : Node := Node.leaf L749
theorem T749_ok : Node.check D_R22222 T749 [((0),(163/256)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L749_ok
def T748 : Node := Node.split 0 T749 T750
theorem T748_ok : Node.check D_R22222 T748 [((0),(163/128)),((405/256),(1215/512)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T749_ok T750_ok
def T747 : Node := Node.leaf L747
theorem T747_ok : Node.check D_R22222 T747 [((0),(163/128)),((405/256),(1215/512)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L747_ok
def T746 : Node := Node.split 2 T747 T748
theorem T746_ok : Node.check D_R22222 T746 [((0),(163/128)),((405/256),(1215/512)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T747_ok T748_ok
def T745 : Node := Node.split 1 T746 T829
theorem T745_ok : Node.check D_R22222 T745 [((0),(163/128)),((405/256),(405/128)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T746_ok T829_ok
def T744 : Node := Node.split 3 T745 T886
theorem T744_ok : Node.check D_R22222 T744 [((0),(163/128)),((405/256),(405/128)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T745_ok T886_ok
def T743 : Node := Node.split 0 T744 T1021
theorem T743_ok : Node.check D_R22222 T743 [((0),(163/64)),((405/256),(405/128)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T744_ok T1021_ok
def T742 : Node := Node.split 2 T743 T1246
theorem T742_ok : Node.check D_R22222 T742 [((0),(163/64)),((405/256),(405/128)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T743_ok T1246_ok
def T741 : Node := Node.leaf L741
theorem T741_ok : Node.check D_R22222 T741 [((489/256),(163/64)),((1215/1024),(405/256)),((1215/512),(405/128)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L741_ok
def T740 : Node := Node.leaf L740
theorem T740_ok : Node.check D_R22222 T740 [((489/256),(163/64)),((405/512),(1215/1024)),((2835/1024),(405/128)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L740_ok
def T739 : Node := Node.leaf L739
theorem T739_ok : Node.check D_R22222 T739 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/512),(2835/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L739_ok
def T738 : Node := Node.split 2 T739 T740
theorem T738_ok : Node.check D_R22222 T738 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/512),(405/128)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T739_ok T740_ok
def T737 : Node := Node.split 1 T738 T741
theorem T737_ok : Node.check D_R22222 T737 [((489/256),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T738_ok T741_ok
def T736 : Node := Node.leaf L736
theorem T736_ok : Node.check D_R22222 T736 [((489/256),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L736_ok
def T735 : Node := Node.split 3 T736 T737
theorem T735_ok : Node.check D_R22222 T735 [((489/256),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T736_ok T737_ok
def T734 : Node := Node.leaf L734
theorem T734_ok : Node.check D_R22222 T734 [((163/128),(489/256)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L734_ok
def T733 : Node := Node.split 0 T734 T735
theorem T733_ok : Node.check D_R22222 T733 [((163/128),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T734_ok T735_ok
def T732 : Node := Node.leaf L732
theorem T732_ok : Node.check D_R22222 T732 [((489/256),(163/64)),((1215/1024),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L732_ok
def T731 : Node := Node.leaf L731
theorem T731_ok : Node.check D_R22222 T731 [((1141/512),(163/64)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L731_ok
def T730 : Node := Node.leaf L730
theorem T730_ok : Node.check D_R22222 T730 [((489/256),(1141/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L730_ok
def T729 : Node := Node.leaf L729
theorem T729_ok : Node.check D_R22222 T729 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((4455/2048),(1215/512)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L729_ok
def T728 : Node := Node.leaf L728
theorem T728_ok : Node.check D_R22222 T728 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L728_ok
def T727 : Node := Node.leaf L727
theorem T727_ok : Node.check D_R22222 T727 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L727_ok
def T726 : Node := Node.leaf L726
theorem T726_ok : Node.check D_R22222 T726 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L726_ok
def T725 : Node := Node.split 2 T726 T727
theorem T725_ok : Node.check D_R22222 T725 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T726_ok T727_ok
def T724 : Node := Node.split 1 T725 T728
theorem T724_ok : Node.check D_R22222 T724 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T725_ok T728_ok
def T723 : Node := Node.leaf L723
theorem T723_ok : Node.check D_R22222 T723 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L723_ok
def T722 : Node := Node.leaf L722
theorem T722_ok : Node.check D_R22222 T722 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L722_ok
def T721 : Node := Node.leaf L721
theorem T721_ok : Node.check D_R22222 T721 [((4401/2048),(1141/512)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L721_ok
def T720 : Node := Node.leaf L720
theorem T720_ok : Node.check D_R22222 T720 [((2119/1024),(4401/2048)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L720_ok
def T719 : Node := Node.split 0 T720 T721
theorem T719_ok : Node.check D_R22222 T719 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T720_ok T721_ok
def T718 : Node := Node.split 2 T719 T722
theorem T718_ok : Node.check D_R22222 T718 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T719_ok T722_ok
def T717 : Node := Node.split 1 T718 T723
theorem T717_ok : Node.check D_R22222 T717 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T718_ok T723_ok
def T716 : Node := Node.split 3 T717 T724
theorem T716_ok : Node.check D_R22222 T716 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T717_ok T724_ok
def T715 : Node := Node.leaf L715
theorem T715_ok : Node.check D_R22222 T715 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L715_ok
def T714 : Node := Node.leaf L714
theorem T714_ok : Node.check D_R22222 T714 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L714_ok
def T713 : Node := Node.leaf L713
theorem T713_ok : Node.check D_R22222 T713 [((4075/2048),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L713_ok
def T712 : Node := Node.leaf L712
theorem T712_ok : Node.check D_R22222 T712 [((489/256),(4075/2048)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L712_ok
def T711 : Node := Node.split 0 T712 T713
theorem T711_ok : Node.check D_R22222 T711 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T712_ok T713_ok
def T710 : Node := Node.split 2 T711 T714
theorem T710_ok : Node.check D_R22222 T710 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T711_ok T714_ok
def T709 : Node := Node.split 1 T710 T715
theorem T709_ok : Node.check D_R22222 T709 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T710_ok T715_ok
def T708 : Node := Node.leaf L708
theorem T708_ok : Node.check D_R22222 T708 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((8505/4096),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L708_ok
def T707 : Node := Node.leaf L707
theorem T707_ok : Node.check D_R22222 T707 [((4075/2048),(2119/1024)),((9315/8192),(1215/1024)),((2025/1024),(8505/4096)),((4075/2048),(2119/1024))] = true := Node.check_leaf_of _ _ _ L707_ok
def T706 : Node := Node.leaf L706
theorem T706_ok : Node.check D_R22222 T706 [((4075/2048),(2119/1024)),((4455/4096),(9315/8192)),((2025/1024),(8505/4096)),((4075/2048),(2119/1024))] = true := Node.check_leaf_of _ _ _ L706_ok
def T705 : Node := Node.split 1 T706 T707
theorem T705_ok : Node.check D_R22222 T705 [((4075/2048),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((4075/2048),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T706_ok T707_ok
def T704 : Node := Node.leaf L704
theorem T704_ok : Node.check D_R22222 T704 [((4075/2048),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/256),(4075/2048))] = true := Node.check_leaf_of _ _ _ L704_ok
def T703 : Node := Node.split 3 T704 T705
theorem T703_ok : Node.check D_R22222 T703 [((4075/2048),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T704_ok T705_ok
def T702 : Node := Node.leaf L702
theorem T702_ok : Node.check D_R22222 T702 [((489/256),(4075/2048)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L702_ok
def T701 : Node := Node.split 0 T702 T703
theorem T701_ok : Node.check D_R22222 T701 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T702_ok T703_ok
def T700 : Node := Node.split 2 T701 T708
theorem T700_ok : Node.check D_R22222 T700 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T701_ok T708_ok
def T699 : Node := Node.leaf L699
theorem T699_ok : Node.check D_R22222 T699 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L699_ok
def T698 : Node := Node.leaf L698
theorem T698_ok : Node.check D_R22222 T698 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L698_ok
def T697 : Node := Node.split 2 T698 T699
theorem T697_ok : Node.check D_R22222 T697 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T698_ok T699_ok
def T696 : Node := Node.split 1 T697 T700
theorem T696_ok : Node.check D_R22222 T696 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T697_ok T700_ok
def T695 : Node := Node.split 3 T696 T709
theorem T695_ok : Node.check D_R22222 T695 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T696_ok T709_ok
def T694 : Node := Node.split 0 T695 T716
theorem T694_ok : Node.check D_R22222 T694 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T695_ok T716_ok
def T693 : Node := Node.split 2 T694 T729
theorem T693_ok : Node.check D_R22222 T693 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T694_ok T729_ok
def T692 : Node := Node.leaf L692
theorem T692_ok : Node.check D_R22222 T692 [((489/256),(1141/512)),((405/512),(2025/2048)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L692_ok
def T691 : Node := Node.split 1 T692 T693
theorem T691_ok : Node.check D_R22222 T691 [((489/256),(1141/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T692_ok T693_ok
def T690 : Node := Node.split 3 T691 T730
theorem T690_ok : Node.check D_R22222 T690 [((489/256),(1141/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T691_ok T730_ok
def T689 : Node := Node.split 0 T690 T731
theorem T689_ok : Node.check D_R22222 T689 [((489/256),(163/64)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T690_ok T731_ok
def T688 : Node := Node.leaf L688
theorem T688_ok : Node.check D_R22222 T688 [((1141/512),(163/64)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L688_ok
def T687 : Node := Node.leaf L687
theorem T687_ok : Node.check D_R22222 T687 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/256),(2025/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L687_ok
def T686 : Node := Node.leaf L686
theorem T686_ok : Node.check D_R22222 T686 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L686_ok
def T685 : Node := Node.leaf L685
theorem T685_ok : Node.check D_R22222 T685 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L685_ok
def T684 : Node := Node.leaf L684
theorem T684_ok : Node.check D_R22222 T684 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L684_ok
def T683 : Node := Node.leaf L683
theorem T683_ok : Node.check D_R22222 T683 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L683_ok
def T682 : Node := Node.split 1 T683 T684
theorem T682_ok : Node.check D_R22222 T682 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T683_ok T684_ok
def T681 : Node := Node.split 3 T682 T685
theorem T681_ok : Node.check D_R22222 T681 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T682_ok T685_ok
def T680 : Node := Node.split 0 T681 T686
theorem T680_ok : Node.check D_R22222 T680 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T681_ok T686_ok
def T679 : Node := Node.leaf L679
theorem T679_ok : Node.check D_R22222 T679 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/256),(3645/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L679_ok
def T678 : Node := Node.split 2 T679 T680
theorem T678_ok : Node.check D_R22222 T678 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/256),(2025/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T679_ok T680_ok
def T677 : Node := Node.leaf L677
theorem T677_ok : Node.check D_R22222 T677 [((489/256),(1141/512)),((405/512),(2025/2048)),((405/256),(2025/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L677_ok
def T676 : Node := Node.split 1 T677 T678
theorem T676_ok : Node.check D_R22222 T676 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T677_ok T678_ok
def T675 : Node := Node.split 3 T676 T687
theorem T675_ok : Node.check D_R22222 T675 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T676_ok T687_ok
def T674 : Node := Node.split 0 T675 T688
theorem T674_ok : Node.check D_R22222 T674 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T675_ok T688_ok
def T673 : Node := Node.split 2 T674 T689
theorem T673_ok : Node.check D_R22222 T673 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T674_ok T689_ok
def T672 : Node := Node.split 1 T673 T732
theorem T672_ok : Node.check D_R22222 T672 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T673_ok T732_ok
def T671 : Node := Node.leaf L671
theorem T671_ok : Node.check D_R22222 T671 [((489/256),(163/64)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L671_ok
def T670 : Node := Node.leaf L670
theorem T670_ok : Node.check D_R22222 T670 [((489/256),(163/64)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L670_ok
def T669 : Node := Node.leaf L669
theorem T669_ok : Node.check D_R22222 T669 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L669_ok
def T668 : Node := Node.split 2 T669 T670
theorem T668_ok : Node.check D_R22222 T668 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T669_ok T670_ok
def T667 : Node := Node.split 1 T668 T671
theorem T667_ok : Node.check D_R22222 T667 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T668_ok T671_ok
def T666 : Node := Node.split 3 T667 T672
theorem T666_ok : Node.check D_R22222 T666 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T667_ok T672_ok
def T665 : Node := Node.leaf L665
theorem T665_ok : Node.check D_R22222 T665 [((163/128),(489/256)),((1215/1024),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L665_ok
def T664 : Node := Node.leaf L664
theorem T664_ok : Node.check D_R22222 T664 [((163/128),(489/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L664_ok
def T663 : Node := Node.leaf L663
theorem T663_ok : Node.check D_R22222 T663 [((163/128),(489/256)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L663_ok
def T662 : Node := Node.split 2 T663 T664
theorem T662_ok : Node.check D_R22222 T662 [((163/128),(489/256)),((405/512),(1215/1024)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T663_ok T664_ok
def T661 : Node := Node.split 1 T662 T665
theorem T661_ok : Node.check D_R22222 T661 [((163/128),(489/256)),((405/512),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T662_ok T665_ok
def T660 : Node := Node.leaf L660
theorem T660_ok : Node.check D_R22222 T660 [((163/128),(489/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L660_ok
def T659 : Node := Node.split 3 T660 T661
theorem T659_ok : Node.check D_R22222 T659 [((163/128),(489/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T660_ok T661_ok
def T658 : Node := Node.split 0 T659 T666
theorem T658_ok : Node.check D_R22222 T658 [((163/128),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T659_ok T666_ok
def T657 : Node := Node.split 2 T658 T733
theorem T657_ok : Node.check D_R22222 T657 [((163/128),(163/64)),((405/512),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T658_ok T733_ok
def T656 : Node := Node.leaf L656
theorem T656_ok : Node.check D_R22222 T656 [((163/128),(163/64)),((0),(405/512)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L656_ok
def T655 : Node := Node.split 1 T656 T657
theorem T655_ok : Node.check D_R22222 T655 [((163/128),(163/64)),((0),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T656_ok T657_ok
def T654 : Node := Node.leaf L654
theorem T654_ok : Node.check D_R22222 T654 [((489/256),(163/64)),((1215/1024),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L654_ok
def T653 : Node := Node.leaf L653
theorem T653_ok : Node.check D_R22222 T653 [((1141/512),(163/64)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L653_ok
def T652 : Node := Node.leaf L652
theorem T652_ok : Node.check D_R22222 T652 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L652_ok
def T651 : Node := Node.leaf L651
theorem T651_ok : Node.check D_R22222 T651 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((6075/2048),(405/128)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L651_ok
def T650 : Node := Node.leaf L650
theorem T650_ok : Node.check D_R22222 T650 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((12555/4096),(405/128)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L650_ok
def T649 : Node := Node.leaf L649
theorem T649_ok : Node.check D_R22222 T649 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((6075/2048),(12555/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L649_ok
def T648 : Node := Node.split 2 T649 T650
theorem T648_ok : Node.check D_R22222 T648 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((6075/2048),(405/128)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T649_ok T650_ok
def T647 : Node := Node.split 1 T648 T651
theorem T647_ok : Node.check D_R22222 T647 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T648_ok T651_ok
def T646 : Node := Node.split 3 T647 T652
theorem T646_ok : Node.check D_R22222 T646 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T647_ok T652_ok
def T645 : Node := Node.leaf L645
theorem T645_ok : Node.check D_R22222 T645 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L645_ok
def T644 : Node := Node.leaf L644
theorem T644_ok : Node.check D_R22222 T644 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((12555/4096),(405/128)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L644_ok
def T643 : Node := Node.leaf L643
theorem T643_ok : Node.check D_R22222 T643 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((6075/2048),(12555/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L643_ok
def T642 : Node := Node.split 2 T643 T644
theorem T642_ok : Node.check D_R22222 T642 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((6075/2048),(405/128)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T643_ok T644_ok
def T641 : Node := Node.leaf L641
theorem T641_ok : Node.check D_R22222 T641 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((12555/4096),(405/128)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L641_ok
def T640 : Node := Node.leaf L640
theorem T640_ok : Node.check D_R22222 T640 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((6075/2048),(12555/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L640_ok
def T639 : Node := Node.split 2 T640 T641
theorem T639_ok : Node.check D_R22222 T639 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((6075/2048),(405/128)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T640_ok T641_ok
def T638 : Node := Node.split 1 T639 T642
theorem T638_ok : Node.check D_R22222 T638 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T639_ok T642_ok
def T637 : Node := Node.split 3 T638 T645
theorem T637_ok : Node.check D_R22222 T637 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T638_ok T645_ok
def T636 : Node := Node.split 0 T637 T646
theorem T636_ok : Node.check D_R22222 T636 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T637_ok T646_ok
def T635 : Node := Node.leaf L635
theorem T635_ok : Node.check D_R22222 T635 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L635_ok
def T634 : Node := Node.leaf L634
theorem T634_ok : Node.check D_R22222 T634 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L634_ok
def T633 : Node := Node.split 3 T634 T635
theorem T633_ok : Node.check D_R22222 T633 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T634_ok T635_ok
def T632 : Node := Node.leaf L632
theorem T632_ok : Node.check D_R22222 T632 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L632_ok
def T631 : Node := Node.leaf L631
theorem T631_ok : Node.check D_R22222 T631 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L631_ok
def T630 : Node := Node.leaf L630
theorem T630_ok : Node.check D_R22222 T630 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2835/1024),(6075/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L630_ok
def T629 : Node := Node.split 1 T630 T631
theorem T629_ok : Node.check D_R22222 T629 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T630_ok T631_ok
def T628 : Node := Node.split 3 T629 T632
theorem T628_ok : Node.check D_R22222 T628 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T629_ok T632_ok
def T627 : Node := Node.split 0 T628 T633
theorem T627_ok : Node.check D_R22222 T627 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T628_ok T633_ok
def T626 : Node := Node.split 2 T627 T636
theorem T626_ok : Node.check D_R22222 T626 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2835/1024),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T627_ok T636_ok
def T625 : Node := Node.leaf L625
theorem T625_ok : Node.check D_R22222 T625 [((489/256),(1141/512)),((405/512),(2025/2048)),((2835/1024),(405/128)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L625_ok
def T624 : Node := Node.split 1 T625 T626
theorem T624_ok : Node.check D_R22222 T624 [((489/256),(1141/512)),((405/512),(1215/1024)),((2835/1024),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T625_ok T626_ok
def T623 : Node := Node.leaf L623
theorem T623_ok : Node.check D_R22222 T623 [((489/256),(1141/512)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L623_ok
def T622 : Node := Node.split 3 T623 T624
theorem T622_ok : Node.check D_R22222 T622 [((489/256),(1141/512)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T623_ok T624_ok
def T621 : Node := Node.split 0 T622 T653
theorem T621_ok : Node.check D_R22222 T621 [((489/256),(163/64)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T622_ok T653_ok
def T620 : Node := Node.leaf L620
theorem T620_ok : Node.check D_R22222 T620 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/512),(2835/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L620_ok
def T619 : Node := Node.split 2 T620 T621
theorem T619_ok : Node.check D_R22222 T619 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T620_ok T621_ok
def T618 : Node := Node.split 1 T619 T654
theorem T618_ok : Node.check D_R22222 T618 [((489/256),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T619_ok T654_ok
def T617 : Node := Node.leaf L617
theorem T617_ok : Node.check D_R22222 T617 [((489/256),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L617_ok
def T616 : Node := Node.split 3 T617 T618
theorem T616_ok : Node.check D_R22222 T616 [((489/256),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T617_ok T618_ok
def T615 : Node := Node.leaf L615
theorem T615_ok : Node.check D_R22222 T615 [((163/128),(489/256)),((1215/1024),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L615_ok
def T614 : Node := Node.leaf L614
theorem T614_ok : Node.check D_R22222 T614 [((163/128),(489/256)),((405/512),(1215/1024)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L614_ok
def T613 : Node := Node.split 1 T614 T615
theorem T613_ok : Node.check D_R22222 T613 [((163/128),(489/256)),((405/512),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T614_ok T615_ok
def T612 : Node := Node.leaf L612
theorem T612_ok : Node.check D_R22222 T612 [((163/128),(489/256)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L612_ok
def T611 : Node := Node.split 3 T612 T613
theorem T611_ok : Node.check D_R22222 T611 [((163/128),(489/256)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T612_ok T613_ok
def T610 : Node := Node.split 0 T611 T616
theorem T610_ok : Node.check D_R22222 T610 [((163/128),(163/64)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T611_ok T616_ok
def T609 : Node := Node.leaf L609
theorem T609_ok : Node.check D_R22222 T609 [((489/256),(163/64)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L609_ok
def T608 : Node := Node.leaf L608
theorem T608_ok : Node.check D_R22222 T608 [((1141/512),(163/64)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L608_ok
def T607 : Node := Node.leaf L607
theorem T607_ok : Node.check D_R22222 T607 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((4455/2048),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L607_ok
def T606 : Node := Node.leaf L606
theorem T606_ok : Node.check D_R22222 T606 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L606_ok
def T605 : Node := Node.leaf L605
theorem T605_ok : Node.check D_R22222 T605 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L605_ok
def T604 : Node := Node.leaf L604
theorem T604_ok : Node.check D_R22222 T604 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L604_ok
def T603 : Node := Node.leaf L603
theorem T603_ok : Node.check D_R22222 T603 [((4401/2048),(1141/512)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L603_ok
def T602 : Node := Node.leaf L602
theorem T602_ok : Node.check D_R22222 T602 [((2119/1024),(4401/2048)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L602_ok
def T601 : Node := Node.leaf L601
theorem T601_ok : Node.check D_R22222 T601 [((2119/1024),(4401/2048)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L601_ok
def T600 : Node := Node.split 3 T601 T602
theorem T600_ok : Node.check D_R22222 T600 [((2119/1024),(4401/2048)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T601_ok T602_ok
def T599 : Node := Node.split 0 T600 T603
theorem T599_ok : Node.check D_R22222 T599 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T600_ok T603_ok
def T598 : Node := Node.split 2 T599 T604
theorem T598_ok : Node.check D_R22222 T598 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T599_ok T604_ok
def T597 : Node := Node.split 1 T598 T605
theorem T597_ok : Node.check D_R22222 T597 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T598_ok T605_ok
def T596 : Node := Node.split 3 T597 T606
theorem T596_ok : Node.check D_R22222 T596 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T597_ok T606_ok
def T595 : Node := Node.leaf L595
theorem T595_ok : Node.check D_R22222 T595 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L595_ok
def T594 : Node := Node.leaf L594
theorem T594_ok : Node.check D_R22222 T594 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L594_ok
def T593 : Node := Node.leaf L593
theorem T593_ok : Node.check D_R22222 T593 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L593_ok
def T592 : Node := Node.split 2 T593 T594
theorem T592_ok : Node.check D_R22222 T592 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T593_ok T594_ok
def T591 : Node := Node.split 1 T592 T595
theorem T591_ok : Node.check D_R22222 T591 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T592_ok T595_ok
def T590 : Node := Node.leaf L590
theorem T590_ok : Node.check D_R22222 T590 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L590_ok
def T589 : Node := Node.leaf L589
theorem T589_ok : Node.check D_R22222 T589 [((4075/2048),(2119/1024)),((9315/8192),(1215/1024)),((2025/1024),(8505/4096)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L589_ok
def T588 : Node := Node.leaf L588
theorem T588_ok : Node.check D_R22222 T588 [((4075/2048),(2119/1024)),((4455/4096),(9315/8192)),((2025/1024),(8505/4096)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L588_ok
def T587 : Node := Node.split 1 T588 T589
theorem T587_ok : Node.check D_R22222 T587 [((4075/2048),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((2119/2048),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T588_ok T589_ok
def T586 : Node := Node.leaf L586
theorem T586_ok : Node.check D_R22222 T586 [((4075/2048),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L586_ok
def T585 : Node := Node.split 3 T586 T587
theorem T585_ok : Node.check D_R22222 T585 [((4075/2048),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T586_ok T587_ok
def T584 : Node := Node.leaf L584
theorem T584_ok : Node.check D_R22222 T584 [((489/256),(4075/2048)),((9315/8192),(1215/1024)),((2025/1024),(8505/4096)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L584_ok
def T583 : Node := Node.leaf L583
theorem T583_ok : Node.check D_R22222 T583 [((489/256),(4075/2048)),((4455/4096),(9315/8192)),((2025/1024),(8505/4096)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L583_ok
def T582 : Node := Node.split 1 T583 T584
theorem T582_ok : Node.check D_R22222 T582 [((489/256),(4075/2048)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((2119/2048),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T583_ok T584_ok
def T581 : Node := Node.leaf L581
theorem T581_ok : Node.check D_R22222 T581 [((489/256),(4075/2048)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L581_ok
def T580 : Node := Node.split 3 T581 T582
theorem T580_ok : Node.check D_R22222 T580 [((489/256),(4075/2048)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T581_ok T582_ok
def T579 : Node := Node.split 0 T580 T585
theorem T579_ok : Node.check D_R22222 T579 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T580_ok T585_ok
def T578 : Node := Node.split 2 T579 T590
theorem T578_ok : Node.check D_R22222 T578 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T579_ok T590_ok
def T577 : Node := Node.leaf L577
theorem T577_ok : Node.check D_R22222 T577 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L577_ok
def T576 : Node := Node.leaf L576
theorem T576_ok : Node.check D_R22222 T576 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L576_ok
def T575 : Node := Node.split 2 T576 T577
theorem T575_ok : Node.check D_R22222 T575 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T576_ok T577_ok
def T574 : Node := Node.split 1 T575 T578
theorem T574_ok : Node.check D_R22222 T574 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T575_ok T578_ok
def T573 : Node := Node.split 3 T574 T591
theorem T573_ok : Node.check D_R22222 T573 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T574_ok T591_ok
def T572 : Node := Node.split 0 T573 T596
theorem T572_ok : Node.check D_R22222 T572 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T573_ok T596_ok
def T571 : Node := Node.split 2 T572 T607
theorem T571_ok : Node.check D_R22222 T571 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T572_ok T607_ok
def T570 : Node := Node.leaf L570
theorem T570_ok : Node.check D_R22222 T570 [((489/256),(1141/512)),((405/512),(2025/2048)),((2025/1024),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L570_ok
def T569 : Node := Node.split 1 T570 T571
theorem T569_ok : Node.check D_R22222 T569 [((489/256),(1141/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T570_ok T571_ok
def T568 : Node := Node.leaf L568
theorem T568_ok : Node.check D_R22222 T568 [((489/256),(1141/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L568_ok
def T567 : Node := Node.split 3 T568 T569
theorem T567_ok : Node.check D_R22222 T567 [((489/256),(1141/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T568_ok T569_ok
def T566 : Node := Node.split 0 T567 T608
theorem T566_ok : Node.check D_R22222 T566 [((489/256),(163/64)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T567_ok T608_ok
def T565 : Node := Node.leaf L565
theorem T565_ok : Node.check D_R22222 T565 [((1141/512),(163/64)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L565_ok
def T564 : Node := Node.leaf L564
theorem T564_ok : Node.check D_R22222 T564 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L564_ok
def T563 : Node := Node.leaf L563
theorem T563_ok : Node.check D_R22222 T563 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L563_ok
def T562 : Node := Node.leaf L562
theorem T562_ok : Node.check D_R22222 T562 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((3645/2048),(7695/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L562_ok
def T561 : Node := Node.split 2 T562 T563
theorem T561_ok : Node.check D_R22222 T561 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T562_ok T563_ok
def T560 : Node := Node.split 1 T561 T564
theorem T560_ok : Node.check D_R22222 T560 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T561_ok T564_ok
def T559 : Node := Node.leaf L559
theorem T559_ok : Node.check D_R22222 T559 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L559_ok
def T558 : Node := Node.leaf L558
theorem T558_ok : Node.check D_R22222 T558 [((4401/2048),(1141/512)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L558_ok
def T557 : Node := Node.leaf L557
theorem T557_ok : Node.check D_R22222 T557 [((2119/1024),(4401/2048)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L557_ok
def T556 : Node := Node.split 0 T557 T558
theorem T556_ok : Node.check D_R22222 T556 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T557_ok T558_ok
def T555 : Node := Node.leaf L555
theorem T555_ok : Node.check D_R22222 T555 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((3645/2048),(7695/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L555_ok
def T554 : Node := Node.split 2 T555 T556
theorem T554_ok : Node.check D_R22222 T554 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T555_ok T556_ok
def T553 : Node := Node.split 1 T554 T559
theorem T553_ok : Node.check D_R22222 T553 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T554_ok T559_ok
def T552 : Node := Node.split 3 T553 T560
theorem T552_ok : Node.check D_R22222 T552 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T553_ok T560_ok
def T551 : Node := Node.leaf L551
theorem T551_ok : Node.check D_R22222 T551 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L551_ok
def T550 : Node := Node.leaf L550
theorem T550_ok : Node.check D_R22222 T550 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L550_ok
def T549 : Node := Node.leaf L549
theorem T549_ok : Node.check D_R22222 T549 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((3645/2048),(7695/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L549_ok
def T548 : Node := Node.split 2 T549 T550
theorem T548_ok : Node.check D_R22222 T548 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T549_ok T550_ok
def T547 : Node := Node.split 1 T548 T551
theorem T547_ok : Node.check D_R22222 T547 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T548_ok T551_ok
def T546 : Node := Node.leaf L546
theorem T546_ok : Node.check D_R22222 T546 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L546_ok
def T545 : Node := Node.leaf L545
theorem T545_ok : Node.check D_R22222 T545 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((3645/2048),(7695/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L545_ok
def T544 : Node := Node.split 2 T545 T546
theorem T544_ok : Node.check D_R22222 T544 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T545_ok T546_ok
def T543 : Node := Node.leaf L543
theorem T543_ok : Node.check D_R22222 T543 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L543_ok
def T542 : Node := Node.leaf L542
theorem T542_ok : Node.check D_R22222 T542 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((3645/2048),(7695/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L542_ok
def T541 : Node := Node.split 2 T542 T543
theorem T541_ok : Node.check D_R22222 T541 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T542_ok T543_ok
def T540 : Node := Node.split 1 T541 T544
theorem T540_ok : Node.check D_R22222 T540 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T541_ok T544_ok
def T539 : Node := Node.split 3 T540 T547
theorem T539_ok : Node.check D_R22222 T539 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T540_ok T547_ok
def T538 : Node := Node.split 0 T539 T552
theorem T538_ok : Node.check D_R22222 T538 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T539_ok T552_ok
def T537 : Node := Node.leaf L537
theorem T537_ok : Node.check D_R22222 T537 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/256),(3645/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L537_ok
def T536 : Node := Node.split 2 T537 T538
theorem T536_ok : Node.check D_R22222 T536 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T537_ok T538_ok
def T535 : Node := Node.leaf L535
theorem T535_ok : Node.check D_R22222 T535 [((489/256),(1141/512)),((405/512),(2025/2048)),((405/256),(2025/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L535_ok
def T534 : Node := Node.split 1 T535 T536
theorem T534_ok : Node.check D_R22222 T534 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T535_ok T536_ok
def T533 : Node := Node.leaf L533
theorem T533_ok : Node.check D_R22222 T533 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L533_ok
def T532 : Node := Node.split 3 T533 T534
theorem T532_ok : Node.check D_R22222 T532 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T533_ok T534_ok
def T531 : Node := Node.split 0 T532 T565
theorem T531_ok : Node.check D_R22222 T531 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T532_ok T565_ok
def T530 : Node := Node.split 2 T531 T566
theorem T530_ok : Node.check D_R22222 T530 [((489/256),(163/64)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T531_ok T566_ok
def T529 : Node := Node.split 1 T530 T609
theorem T529_ok : Node.check D_R22222 T529 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T530_ok T609_ok
def T528 : Node := Node.leaf L528
theorem T528_ok : Node.check D_R22222 T528 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L528_ok
def T527 : Node := Node.split 3 T528 T529
theorem T527_ok : Node.check D_R22222 T527 [((489/256),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T528_ok T529_ok
def T526 : Node := Node.leaf L526
theorem T526_ok : Node.check D_R22222 T526 [((163/128),(489/256)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L526_ok
def T525 : Node := Node.leaf L525
theorem T525_ok : Node.check D_R22222 T525 [((815/512),(489/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L525_ok
def T524 : Node := Node.leaf L524
theorem T524_ok : Node.check D_R22222 T524 [((163/128),(815/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L524_ok
def T523 : Node := Node.split 0 T524 T525
theorem T523_ok : Node.check D_R22222 T523 [((163/128),(489/256)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T524_ok T525_ok
def T522 : Node := Node.leaf L522
theorem T522_ok : Node.check D_R22222 T522 [((163/128),(489/256)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L522_ok
def T521 : Node := Node.split 2 T522 T523
theorem T521_ok : Node.check D_R22222 T521 [((163/128),(489/256)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T522_ok T523_ok
def T520 : Node := Node.split 1 T521 T526
theorem T520_ok : Node.check D_R22222 T520 [((163/128),(489/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T521_ok T526_ok
def T519 : Node := Node.leaf L519
theorem T519_ok : Node.check D_R22222 T519 [((163/128),(489/256)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L519_ok
def T518 : Node := Node.split 3 T519 T520
theorem T518_ok : Node.check D_R22222 T518 [((163/128),(489/256)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T519_ok T520_ok
def T517 : Node := Node.split 0 T518 T527
theorem T517_ok : Node.check D_R22222 T517 [((163/128),(163/64)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T518_ok T527_ok
def T516 : Node := Node.split 2 T517 T610
theorem T516_ok : Node.check D_R22222 T516 [((163/128),(163/64)),((405/512),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T517_ok T610_ok
def T515 : Node := Node.leaf L515
theorem T515_ok : Node.check D_R22222 T515 [((163/128),(163/64)),((0),(405/512)),((405/256),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L515_ok
def T514 : Node := Node.split 1 T515 T516
theorem T514_ok : Node.check D_R22222 T514 [((163/128),(163/64)),((0),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T515_ok T516_ok
def T513 : Node := Node.split 3 T514 T655
theorem T513_ok : Node.check D_R22222 T513 [((163/128),(163/64)),((0),(405/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T514_ok T655_ok
def T512 : Node := Node.leaf L512
theorem T512_ok : Node.check D_R22222 T512 [((163/256),(163/128)),((1215/1024),(405/256)),((1215/512),(405/128)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L512_ok
def T511 : Node := Node.leaf L511
theorem T511_ok : Node.check D_R22222 T511 [((489/512),(163/128)),((405/512),(1215/1024)),((2835/1024),(405/128)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L511_ok
def T510 : Node := Node.leaf L510
theorem T510_ok : Node.check D_R22222 T510 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L510_ok
def T509 : Node := Node.leaf L509
theorem T509_ok : Node.check D_R22222 T509 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((6075/2048),(405/128)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L509_ok
def T508 : Node := Node.leaf L508
theorem T508_ok : Node.check D_R22222 T508 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((6075/2048),(405/128)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L508_ok
def T507 : Node := Node.split 1 T508 T509
theorem T507_ok : Node.check D_R22222 T507 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T508_ok T509_ok
def T506 : Node := Node.leaf L506
theorem T506_ok : Node.check D_R22222 T506 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((6075/2048),(405/128)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L506_ok
def T505 : Node := Node.leaf L505
theorem T505_ok : Node.check D_R22222 T505 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((6075/2048),(405/128)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L505_ok
def T504 : Node := Node.split 1 T505 T506
theorem T504_ok : Node.check D_R22222 T504 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T505_ok T506_ok
def T503 : Node := Node.split 3 T504 T507
theorem T503_ok : Node.check D_R22222 T503 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T504_ok T507_ok
def T502 : Node := Node.split 0 T503 T510
theorem T502_ok : Node.check D_R22222 T502 [((489/512),(163/128)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T503_ok T510_ok
def T501 : Node := Node.leaf L501
theorem T501_ok : Node.check D_R22222 T501 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L501_ok
def T500 : Node := Node.leaf L500
theorem T500_ok : Node.check D_R22222 T500 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2835/1024),(6075/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L500_ok
def T499 : Node := Node.leaf L499
theorem T499_ok : Node.check D_R22222 T499 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2835/1024),(6075/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L499_ok
def T498 : Node := Node.split 1 T499 T500
theorem T498_ok : Node.check D_R22222 T498 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T499_ok T500_ok
def T497 : Node := Node.leaf L497
theorem T497_ok : Node.check D_R22222 T497 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2835/1024),(6075/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L497_ok
def T496 : Node := Node.leaf L496
theorem T496_ok : Node.check D_R22222 T496 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2835/1024),(6075/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L496_ok
def T495 : Node := Node.split 1 T496 T497
theorem T495_ok : Node.check D_R22222 T495 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T496_ok T497_ok
def T494 : Node := Node.split 3 T495 T498
theorem T494_ok : Node.check D_R22222 T494 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T495_ok T498_ok
def T493 : Node := Node.split 0 T494 T501
theorem T493_ok : Node.check D_R22222 T493 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T494_ok T501_ok
def T492 : Node := Node.split 2 T493 T502
theorem T492_ok : Node.check D_R22222 T492 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2835/1024),(405/128)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T493_ok T502_ok
def T491 : Node := Node.leaf L491
theorem T491_ok : Node.check D_R22222 T491 [((489/512),(163/128)),((405/512),(2025/2048)),((2835/1024),(405/128)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L491_ok
def T490 : Node := Node.split 1 T491 T492
theorem T490_ok : Node.check D_R22222 T490 [((489/512),(163/128)),((405/512),(1215/1024)),((2835/1024),(405/128)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T491_ok T492_ok
def T489 : Node := Node.split 3 T490 T511
theorem T489_ok : Node.check D_R22222 T489 [((489/512),(163/128)),((405/512),(1215/1024)),((2835/1024),(405/128)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T490_ok T511_ok
def T488 : Node := Node.leaf L488
theorem T488_ok : Node.check D_R22222 T488 [((163/256),(489/512)),((405/512),(1215/1024)),((2835/1024),(405/128)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L488_ok
def T487 : Node := Node.split 0 T488 T489
theorem T487_ok : Node.check D_R22222 T487 [((163/256),(163/128)),((405/512),(1215/1024)),((2835/1024),(405/128)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T488_ok T489_ok
def T486 : Node := Node.leaf L486
theorem T486_ok : Node.check D_R22222 T486 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/512),(2835/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L486_ok
def T485 : Node := Node.split 2 T486 T487
theorem T485_ok : Node.check D_R22222 T485 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/512),(405/128)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T486_ok T487_ok
def T484 : Node := Node.split 1 T485 T512
theorem T484_ok : Node.check D_R22222 T484 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T485_ok T512_ok
def T483 : Node := Node.leaf L483
theorem T483_ok : Node.check D_R22222 T483 [((163/256),(163/128)),((1215/1024),(405/256)),((1215/512),(405/128)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L483_ok
def T482 : Node := Node.leaf L482
theorem T482_ok : Node.check D_R22222 T482 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/512),(405/128)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L482_ok
def T481 : Node := Node.split 1 T482 T483
theorem T481_ok : Node.check D_R22222 T481 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T482_ok T483_ok
def T480 : Node := Node.split 3 T481 T484
theorem T480_ok : Node.check D_R22222 T480 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T481_ok T484_ok
def T479 : Node := Node.leaf L479
theorem T479_ok : Node.check D_R22222 T479 [((0),(163/256)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L479_ok
def T478 : Node := Node.split 0 T479 T480
theorem T478_ok : Node.check D_R22222 T478 [((0),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T479_ok T480_ok
def T477 : Node := Node.leaf L477
theorem T477_ok : Node.check D_R22222 T477 [((163/256),(163/128)),((1215/1024),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L477_ok
def T476 : Node := Node.leaf L476
theorem T476_ok : Node.check D_R22222 T476 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L476_ok
def T475 : Node := Node.leaf L475
theorem T475_ok : Node.check D_R22222 T475 [((489/512),(163/128)),((2025/2048),(1215/1024)),((4455/2048),(1215/512)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L475_ok
def T474 : Node := Node.leaf L474
theorem T474_ok : Node.check D_R22222 T474 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L474_ok
def T473 : Node := Node.leaf L473
theorem T473_ok : Node.check D_R22222 T473 [((1141/1024),(163/128)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L473_ok
def T472 : Node := Node.leaf L472
theorem T472_ok : Node.check D_R22222 T472 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L472_ok
def T471 : Node := Node.split 1 T472 T473
theorem T471_ok : Node.check D_R22222 T471 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T472_ok T473_ok
def T470 : Node := Node.split 3 T471 T474
theorem T470_ok : Node.check D_R22222 T470 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T471_ok T474_ok
def T469 : Node := Node.leaf L469
theorem T469_ok : Node.check D_R22222 T469 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L469_ok
def T468 : Node := Node.leaf L468
theorem T468_ok : Node.check D_R22222 T468 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L468_ok
def T467 : Node := Node.leaf L467
theorem T467_ok : Node.check D_R22222 T467 [((2119/2048),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L467_ok
def T466 : Node := Node.leaf L466
theorem T466_ok : Node.check D_R22222 T466 [((489/512),(2119/2048)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L466_ok
def T465 : Node := Node.split 0 T466 T467
theorem T465_ok : Node.check D_R22222 T465 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T466_ok T467_ok
def T464 : Node := Node.split 2 T465 T468
theorem T464_ok : Node.check D_R22222 T464 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T465_ok T468_ok
def T463 : Node := Node.split 1 T464 T469
theorem T463_ok : Node.check D_R22222 T463 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T464_ok T469_ok
def T462 : Node := Node.leaf L462
theorem T462_ok : Node.check D_R22222 T462 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((8505/4096),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L462_ok
def T461 : Node := Node.leaf L461
theorem T461_ok : Node.check D_R22222 T461 [((2119/2048),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L461_ok
def T460 : Node := Node.leaf L460
theorem T460_ok : Node.check D_R22222 T460 [((489/512),(2119/2048)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L460_ok
def T459 : Node := Node.split 0 T460 T461
theorem T459_ok : Node.check D_R22222 T459 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T460_ok T461_ok
def T458 : Node := Node.split 2 T459 T462
theorem T458_ok : Node.check D_R22222 T458 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T459_ok T462_ok
def T457 : Node := Node.leaf L457
theorem T457_ok : Node.check D_R22222 T457 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L457_ok
def T456 : Node := Node.leaf L456
theorem T456_ok : Node.check D_R22222 T456 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L456_ok
def T455 : Node := Node.split 2 T456 T457
theorem T455_ok : Node.check D_R22222 T455 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T456_ok T457_ok
def T454 : Node := Node.split 1 T455 T458
theorem T454_ok : Node.check D_R22222 T454 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T455_ok T458_ok
def T453 : Node := Node.split 3 T454 T463
theorem T453_ok : Node.check D_R22222 T453 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T454_ok T463_ok
def T452 : Node := Node.split 0 T453 T470
theorem T452_ok : Node.check D_R22222 T452 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T453_ok T470_ok
def T451 : Node := Node.split 2 T452 T475
theorem T451_ok : Node.check D_R22222 T451 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T452_ok T475_ok
def T450 : Node := Node.leaf L450
theorem T450_ok : Node.check D_R22222 T450 [((489/512),(163/128)),((405/512),(2025/2048)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L450_ok
def T449 : Node := Node.split 1 T450 T451
theorem T449_ok : Node.check D_R22222 T449 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T450_ok T451_ok
def T448 : Node := Node.split 3 T449 T476
theorem T448_ok : Node.check D_R22222 T448 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T449_ok T476_ok
def T447 : Node := Node.leaf L447
theorem T447_ok : Node.check D_R22222 T447 [((163/256),(489/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L447_ok
def T446 : Node := Node.split 0 T447 T448
theorem T446_ok : Node.check D_R22222 T446 [((163/256),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T447_ok T448_ok
def T445 : Node := Node.leaf L445
theorem T445_ok : Node.check D_R22222 T445 [((489/512),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L445_ok
def T444 : Node := Node.leaf L444
theorem T444_ok : Node.check D_R22222 T444 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L444_ok
def T443 : Node := Node.leaf L443
theorem T443_ok : Node.check D_R22222 T443 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((7695/4096),(2025/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L443_ok
def T442 : Node := Node.leaf L442
theorem T442_ok : Node.check D_R22222 T442 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((3645/2048),(7695/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L442_ok
def T441 : Node := Node.split 2 T442 T443
theorem T441_ok : Node.check D_R22222 T441 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T442_ok T443_ok
def T440 : Node := Node.leaf L440
theorem T440_ok : Node.check D_R22222 T440 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L440_ok
def T439 : Node := Node.split 1 T440 T441
theorem T439_ok : Node.check D_R22222 T439 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T440_ok T441_ok
def T438 : Node := Node.leaf L438
theorem T438_ok : Node.check D_R22222 T438 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L438_ok
def T437 : Node := Node.leaf L437
theorem T437_ok : Node.check D_R22222 T437 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L437_ok
def T436 : Node := Node.split 1 T437 T438
theorem T436_ok : Node.check D_R22222 T436 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T437_ok T438_ok
def T435 : Node := Node.split 3 T436 T439
theorem T435_ok : Node.check D_R22222 T435 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T436_ok T439_ok
def T434 : Node := Node.split 0 T435 T444
theorem T434_ok : Node.check D_R22222 T434 [((489/512),(163/128)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T435_ok T444_ok
def T433 : Node := Node.leaf L433
theorem T433_ok : Node.check D_R22222 T433 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/256),(3645/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L433_ok
def T432 : Node := Node.split 2 T433 T434
theorem T432_ok : Node.check D_R22222 T432 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/256),(2025/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T433_ok T434_ok
def T431 : Node := Node.leaf L431
theorem T431_ok : Node.check D_R22222 T431 [((489/512),(163/128)),((405/512),(2025/2048)),((405/256),(2025/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L431_ok
def T430 : Node := Node.split 1 T431 T432
theorem T430_ok : Node.check D_R22222 T430 [((489/512),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T431_ok T432_ok
def T429 : Node := Node.split 3 T430 T445
theorem T429_ok : Node.check D_R22222 T429 [((489/512),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T430_ok T445_ok
def T428 : Node := Node.leaf L428
theorem T428_ok : Node.check D_R22222 T428 [((163/256),(489/512)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L428_ok
def T427 : Node := Node.split 0 T428 T429
theorem T427_ok : Node.check D_R22222 T427 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T428_ok T429_ok
def T426 : Node := Node.split 2 T427 T446
theorem T426_ok : Node.check D_R22222 T426 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T427_ok T446_ok
def T425 : Node := Node.split 1 T426 T477
theorem T425_ok : Node.check D_R22222 T425 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T426_ok T477_ok
def T424 : Node := Node.leaf L424
theorem T424_ok : Node.check D_R22222 T424 [((163/256),(163/128)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L424_ok
def T423 : Node := Node.leaf L423
theorem T423_ok : Node.check D_R22222 T423 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((815/512),(489/256))] = true := Node.check_leaf_of _ _ _ L423_ok
def T422 : Node := Node.leaf L422
theorem T422_ok : Node.check D_R22222 T422 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/128),(815/512))] = true := Node.check_leaf_of _ _ _ L422_ok
def T421 : Node := Node.split 3 T422 T423
theorem T421_ok : Node.check D_R22222 T421 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T422_ok T423_ok
def T420 : Node := Node.leaf L420
theorem T420_ok : Node.check D_R22222 T420 [((163/256),(489/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L420_ok
def T419 : Node := Node.split 0 T420 T421
theorem T419_ok : Node.check D_R22222 T419 [((163/256),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T420_ok T421_ok
def T418 : Node := Node.leaf L418
theorem T418_ok : Node.check D_R22222 T418 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L418_ok
def T417 : Node := Node.split 2 T418 T419
theorem T417_ok : Node.check D_R22222 T417 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T418_ok T419_ok
def T416 : Node := Node.split 1 T417 T424
theorem T416_ok : Node.check D_R22222 T416 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T417_ok T424_ok
def T415 : Node := Node.split 3 T416 T425
theorem T415_ok : Node.check D_R22222 T415 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T416_ok T425_ok
def T414 : Node := Node.leaf L414
theorem T414_ok : Node.check D_R22222 T414 [((0),(163/256)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L414_ok
def T413 : Node := Node.split 0 T414 T415
theorem T413_ok : Node.check D_R22222 T413 [((0),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T414_ok T415_ok
def T412 : Node := Node.split 2 T413 T478
theorem T412_ok : Node.check D_R22222 T412 [((0),(163/128)),((405/512),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T413_ok T478_ok
def T411 : Node := Node.leaf L411
theorem T411_ok : Node.check D_R22222 T411 [((0),(163/128)),((0),(405/512)),((405/256),(405/128)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L411_ok
def T410 : Node := Node.split 1 T411 T412
theorem T410_ok : Node.check D_R22222 T410 [((0),(163/128)),((0),(405/256)),((405/256),(405/128)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T411_ok T412_ok
def T409 : Node := Node.leaf L409
theorem T409_ok : Node.check D_R22222 T409 [((163/256),(163/128)),((1215/1024),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L409_ok
def T408 : Node := Node.leaf L408
theorem T408_ok : Node.check D_R22222 T408 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L408_ok
def T407 : Node := Node.leaf L407
theorem T407_ok : Node.check D_R22222 T407 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((6075/2048),(405/128)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L407_ok
def T406 : Node := Node.leaf L406
theorem T406_ok : Node.check D_R22222 T406 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((6075/2048),(405/128)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L406_ok
def T405 : Node := Node.split 1 T406 T407
theorem T405_ok : Node.check D_R22222 T405 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T406_ok T407_ok
def T404 : Node := Node.leaf L404
theorem T404_ok : Node.check D_R22222 T404 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((12555/4096),(405/128)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L404_ok
def T403 : Node := Node.leaf L403
theorem T403_ok : Node.check D_R22222 T403 [((2119/2048),(1141/1024)),((4455/4096),(1215/1024)),((6075/2048),(12555/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L403_ok
def T402 : Node := Node.leaf L402
theorem T402_ok : Node.check D_R22222 T402 [((489/512),(2119/2048)),((4455/4096),(1215/1024)),((6075/2048),(12555/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L402_ok
def T401 : Node := Node.split 0 T402 T403
theorem T401_ok : Node.check D_R22222 T401 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((6075/2048),(12555/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T402_ok T403_ok
def T400 : Node := Node.split 2 T401 T404
theorem T400_ok : Node.check D_R22222 T400 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((6075/2048),(405/128)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T401_ok T404_ok
def T399 : Node := Node.leaf L399
theorem T399_ok : Node.check D_R22222 T399 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((12555/4096),(405/128)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L399_ok
def T398 : Node := Node.leaf L398
theorem T398_ok : Node.check D_R22222 T398 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((6075/2048),(12555/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L398_ok
def T397 : Node := Node.split 2 T398 T399
theorem T397_ok : Node.check D_R22222 T397 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((6075/2048),(405/128)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T398_ok T399_ok
def T396 : Node := Node.split 1 T397 T400
theorem T396_ok : Node.check D_R22222 T396 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T397_ok T400_ok
def T395 : Node := Node.split 3 T396 T405
theorem T395_ok : Node.check D_R22222 T395 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T396_ok T405_ok
def T394 : Node := Node.split 0 T395 T408
theorem T394_ok : Node.check D_R22222 T394 [((489/512),(163/128)),((2025/2048),(1215/1024)),((6075/2048),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T395_ok T408_ok
def T393 : Node := Node.leaf L393
theorem T393_ok : Node.check D_R22222 T393 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L393_ok
def T392 : Node := Node.leaf L392
theorem T392_ok : Node.check D_R22222 T392 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2835/1024),(6075/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L392_ok
def T391 : Node := Node.leaf L391
theorem T391_ok : Node.check D_R22222 T391 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2835/1024),(6075/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L391_ok
def T390 : Node := Node.split 1 T391 T392
theorem T390_ok : Node.check D_R22222 T390 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T391_ok T392_ok
def T389 : Node := Node.leaf L389
theorem T389_ok : Node.check D_R22222 T389 [((2119/2048),(1141/1024)),((4455/4096),(1215/1024)),((11745/4096),(6075/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L389_ok
def T388 : Node := Node.leaf L388
theorem T388_ok : Node.check D_R22222 T388 [((489/512),(2119/2048)),((4455/4096),(1215/1024)),((11745/4096),(6075/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L388_ok
def T387 : Node := Node.split 0 T388 T389
theorem T387_ok : Node.check D_R22222 T387 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((11745/4096),(6075/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T388_ok T389_ok
def T386 : Node := Node.leaf L386
theorem T386_ok : Node.check D_R22222 T386 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2835/1024),(11745/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L386_ok
def T385 : Node := Node.split 2 T386 T387
theorem T385_ok : Node.check D_R22222 T385 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T386_ok T387_ok
def T384 : Node := Node.leaf L384
theorem T384_ok : Node.check D_R22222 T384 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2835/1024),(6075/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L384_ok
def T383 : Node := Node.split 1 T384 T385
theorem T383_ok : Node.check D_R22222 T383 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T384_ok T385_ok
def T382 : Node := Node.split 3 T383 T390
theorem T382_ok : Node.check D_R22222 T382 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T383_ok T390_ok
def T381 : Node := Node.split 0 T382 T393
theorem T381_ok : Node.check D_R22222 T381 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2835/1024),(6075/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T382_ok T393_ok
def T380 : Node := Node.split 2 T381 T394
theorem T380_ok : Node.check D_R22222 T380 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2835/1024),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T381_ok T394_ok
def T379 : Node := Node.leaf L379
theorem T379_ok : Node.check D_R22222 T379 [((489/512),(163/128)),((405/512),(2025/2048)),((2835/1024),(405/128)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L379_ok
def T378 : Node := Node.split 1 T379 T380
theorem T378_ok : Node.check D_R22222 T378 [((489/512),(163/128)),((405/512),(1215/1024)),((2835/1024),(405/128)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T379_ok T380_ok
def T377 : Node := Node.leaf L377
theorem T377_ok : Node.check D_R22222 T377 [((489/512),(163/128)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L377_ok
def T376 : Node := Node.split 3 T377 T378
theorem T376_ok : Node.check D_R22222 T376 [((489/512),(163/128)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T377_ok T378_ok
def T375 : Node := Node.leaf L375
theorem T375_ok : Node.check D_R22222 T375 [((163/256),(489/512)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L375_ok
def T374 : Node := Node.split 0 T375 T376
theorem T374_ok : Node.check D_R22222 T374 [((163/256),(163/128)),((405/512),(1215/1024)),((2835/1024),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T375_ok T376_ok
def T373 : Node := Node.leaf L373
theorem T373_ok : Node.check D_R22222 T373 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/512),(2835/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L373_ok
def T372 : Node := Node.split 2 T373 T374
theorem T372_ok : Node.check D_R22222 T372 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T373_ok T374_ok
def T371 : Node := Node.split 1 T372 T409
theorem T371_ok : Node.check D_R22222 T371 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T372_ok T409_ok
def T370 : Node := Node.leaf L370
theorem T370_ok : Node.check D_R22222 T370 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L370_ok
def T369 : Node := Node.split 3 T370 T371
theorem T369_ok : Node.check D_R22222 T369 [((163/256),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T370_ok T371_ok
def T368 : Node := Node.leaf L368
theorem T368_ok : Node.check D_R22222 T368 [((0),(163/256)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L368_ok
def T367 : Node := Node.split 0 T368 T369
theorem T367_ok : Node.check D_R22222 T367 [((0),(163/128)),((405/512),(405/256)),((1215/512),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T368_ok T369_ok
def T366 : Node := Node.leaf L366
theorem T366_ok : Node.check D_R22222 T366 [((163/256),(163/128)),((1215/1024),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L366_ok
def T365 : Node := Node.leaf L365
theorem T365_ok : Node.check D_R22222 T365 [((489/512),(163/128)),((2025/2048),(1215/1024)),((4455/2048),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L365_ok
def T364 : Node := Node.leaf L364
theorem T364_ok : Node.check D_R22222 T364 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L364_ok
def T363 : Node := Node.leaf L363
theorem T363_ok : Node.check D_R22222 T363 [((1141/1024),(163/128)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L363_ok
def T362 : Node := Node.leaf L362
theorem T362_ok : Node.check D_R22222 T362 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L362_ok
def T361 : Node := Node.leaf L361
theorem T361_ok : Node.check D_R22222 T361 [((2445/2048),(163/128)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L361_ok
def T360 : Node := Node.leaf L360
theorem T360_ok : Node.check D_R22222 T360 [((1141/1024),(2445/2048)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L360_ok
def T359 : Node := Node.split 0 T360 T361
theorem T359_ok : Node.check D_R22222 T359 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T360_ok T361_ok
def T358 : Node := Node.split 2 T359 T362
theorem T358_ok : Node.check D_R22222 T358 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T359_ok T362_ok
def T357 : Node := Node.split 1 T358 T363
theorem T357_ok : Node.check D_R22222 T357 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T358_ok T363_ok
def T356 : Node := Node.split 3 T357 T364
theorem T356_ok : Node.check D_R22222 T356 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T357_ok T364_ok
def T355 : Node := Node.leaf L355
theorem T355_ok : Node.check D_R22222 T355 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L355_ok
def T354 : Node := Node.leaf L354
theorem T354_ok : Node.check D_R22222 T354 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L354_ok
def T353 : Node := Node.leaf L353
theorem T353_ok : Node.check D_R22222 T353 [((2119/2048),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L353_ok
def T352 : Node := Node.leaf L352
theorem T352_ok : Node.check D_R22222 T352 [((489/512),(2119/2048)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L352_ok
def T351 : Node := Node.split 0 T352 T353
theorem T351_ok : Node.check D_R22222 T351 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T352_ok T353_ok
def T350 : Node := Node.split 2 T351 T354
theorem T350_ok : Node.check D_R22222 T350 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T351_ok T354_ok
def T349 : Node := Node.split 1 T350 T355
theorem T349_ok : Node.check D_R22222 T349 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T350_ok T355_ok
def T348 : Node := Node.leaf L348
theorem T348_ok : Node.check D_R22222 T348 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L348_ok
def T347 : Node := Node.leaf L347
theorem T347_ok : Node.check D_R22222 T347 [((2119/2048),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((2119/2048),(1141/1024))] = true := Node.check_leaf_of _ _ _ L347_ok
def T346 : Node := Node.leaf L346
theorem T346_ok : Node.check D_R22222 T346 [((2119/2048),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(2119/2048))] = true := Node.check_leaf_of _ _ _ L346_ok
def T345 : Node := Node.split 3 T346 T347
theorem T345_ok : Node.check D_R22222 T345 [((2119/2048),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T346_ok T347_ok
def T344 : Node := Node.leaf L344
theorem T344_ok : Node.check D_R22222 T344 [((489/512),(2119/2048)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L344_ok
def T343 : Node := Node.split 0 T344 T345
theorem T343_ok : Node.check D_R22222 T343 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T344_ok T345_ok
def T342 : Node := Node.split 2 T343 T348
theorem T342_ok : Node.check D_R22222 T342 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T343_ok T348_ok
def T341 : Node := Node.leaf L341
theorem T341_ok : Node.check D_R22222 T341 [((2119/2048),(1141/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L341_ok
def T340 : Node := Node.leaf L340
theorem T340_ok : Node.check D_R22222 T340 [((489/512),(2119/2048)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L340_ok
def T339 : Node := Node.split 0 T340 T341
theorem T339_ok : Node.check D_R22222 T339 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((8505/4096),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T340_ok T341_ok
def T338 : Node := Node.leaf L338
theorem T338_ok : Node.check D_R22222 T338 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(8505/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L338_ok
def T337 : Node := Node.split 2 T338 T339
theorem T337_ok : Node.check D_R22222 T337 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T338_ok T339_ok
def T336 : Node := Node.split 1 T337 T342
theorem T336_ok : Node.check D_R22222 T336 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T337_ok T342_ok
def T335 : Node := Node.split 3 T336 T349
theorem T335_ok : Node.check D_R22222 T335 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T336_ok T349_ok
def T334 : Node := Node.split 0 T335 T356
theorem T334_ok : Node.check D_R22222 T334 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(4455/2048)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T335_ok T356_ok
def T333 : Node := Node.split 2 T334 T365
theorem T333_ok : Node.check D_R22222 T333 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T334_ok T365_ok
def T332 : Node := Node.leaf L332
theorem T332_ok : Node.check D_R22222 T332 [((489/512),(163/128)),((405/512),(2025/2048)),((2025/1024),(1215/512)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L332_ok
def T331 : Node := Node.split 1 T332 T333
theorem T331_ok : Node.check D_R22222 T331 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T332_ok T333_ok
def T330 : Node := Node.leaf L330
theorem T330_ok : Node.check D_R22222 T330 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L330_ok
def T329 : Node := Node.split 3 T330 T331
theorem T329_ok : Node.check D_R22222 T329 [((489/512),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T330_ok T331_ok
def T328 : Node := Node.leaf L328
theorem T328_ok : Node.check D_R22222 T328 [((163/256),(489/512)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L328_ok
def T327 : Node := Node.split 0 T328 T329
theorem T327_ok : Node.check D_R22222 T327 [((163/256),(163/128)),((405/512),(1215/1024)),((2025/1024),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T328_ok T329_ok
def T326 : Node := Node.leaf L326
theorem T326_ok : Node.check D_R22222 T326 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L326_ok
def T325 : Node := Node.leaf L325
theorem T325_ok : Node.check D_R22222 T325 [((1141/1024),(163/128)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L325_ok
def T324 : Node := Node.leaf L324
theorem T324_ok : Node.check D_R22222 T324 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L324_ok
def T323 : Node := Node.leaf L323
theorem T323_ok : Node.check D_R22222 T323 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((3645/2048),(7695/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L323_ok
def T322 : Node := Node.split 2 T323 T324
theorem T322_ok : Node.check D_R22222 T322 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T323_ok T324_ok
def T321 : Node := Node.split 1 T322 T325
theorem T321_ok : Node.check D_R22222 T321 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T322_ok T325_ok
def T320 : Node := Node.split 3 T321 T326
theorem T320_ok : Node.check D_R22222 T320 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T321_ok T326_ok
def T319 : Node := Node.leaf L319
theorem T319_ok : Node.check D_R22222 T319 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((7695/4096),(2025/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L319_ok
def T318 : Node := Node.leaf L318
theorem T318_ok : Node.check D_R22222 T318 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((3645/2048),(7695/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L318_ok
def T317 : Node := Node.split 2 T318 T319
theorem T317_ok : Node.check D_R22222 T317 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T318_ok T319_ok
def T316 : Node := Node.leaf L316
theorem T316_ok : Node.check D_R22222 T316 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L316_ok
def T315 : Node := Node.leaf L315
theorem T315_ok : Node.check D_R22222 T315 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((3645/2048),(7695/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L315_ok
def T314 : Node := Node.split 2 T315 T316
theorem T314_ok : Node.check D_R22222 T314 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T315_ok T316_ok
def T313 : Node := Node.split 1 T314 T317
theorem T313_ok : Node.check D_R22222 T313 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T314_ok T317_ok
def T312 : Node := Node.leaf L312
theorem T312_ok : Node.check D_R22222 T312 [((2119/2048),(1141/1024)),((4455/4096),(1215/1024)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L312_ok
def T311 : Node := Node.leaf L311
theorem T311_ok : Node.check D_R22222 T311 [((489/512),(2119/2048)),((4455/4096),(1215/1024)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L311_ok
def T310 : Node := Node.split 0 T311 T312
theorem T310_ok : Node.check D_R22222 T310 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T311_ok T312_ok
def T309 : Node := Node.leaf L309
theorem T309_ok : Node.check D_R22222 T309 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((3645/2048),(7695/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L309_ok
def T308 : Node := Node.split 2 T309 T310
theorem T308_ok : Node.check D_R22222 T308 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T309_ok T310_ok
def T307 : Node := Node.leaf L307
theorem T307_ok : Node.check D_R22222 T307 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((7695/4096),(2025/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L307_ok
def T306 : Node := Node.leaf L306
theorem T306_ok : Node.check D_R22222 T306 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((3645/2048),(7695/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L306_ok
def T305 : Node := Node.split 2 T306 T307
theorem T305_ok : Node.check D_R22222 T305 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T306_ok T307_ok
def T304 : Node := Node.split 1 T305 T308
theorem T304_ok : Node.check D_R22222 T304 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T305_ok T308_ok
def T303 : Node := Node.split 3 T304 T313
theorem T303_ok : Node.check D_R22222 T303 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T304_ok T313_ok
def T302 : Node := Node.split 0 T303 T320
theorem T302_ok : Node.check D_R22222 T302 [((489/512),(163/128)),((2025/2048),(1215/1024)),((3645/2048),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T303_ok T320_ok
def T301 : Node := Node.leaf L301
theorem T301_ok : Node.check D_R22222 T301 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/256),(3645/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L301_ok
def T300 : Node := Node.split 2 T301 T302
theorem T300_ok : Node.check D_R22222 T300 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T301_ok T302_ok
def T299 : Node := Node.leaf L299
theorem T299_ok : Node.check D_R22222 T299 [((489/512),(163/128)),((405/512),(2025/2048)),((405/256),(2025/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L299_ok
def T298 : Node := Node.split 1 T299 T300
theorem T298_ok : Node.check D_R22222 T298 [((489/512),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T299_ok T300_ok
def T297 : Node := Node.leaf L297
theorem T297_ok : Node.check D_R22222 T297 [((489/512),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L297_ok
def T296 : Node := Node.split 3 T297 T298
theorem T296_ok : Node.check D_R22222 T296 [((489/512),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T297_ok T298_ok
def T295 : Node := Node.leaf L295
theorem T295_ok : Node.check D_R22222 T295 [((163/256),(489/512)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L295_ok
def T294 : Node := Node.split 0 T295 T296
theorem T294_ok : Node.check D_R22222 T294 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(2025/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T295_ok T296_ok
def T293 : Node := Node.split 2 T294 T327
theorem T293_ok : Node.check D_R22222 T293 [((163/256),(163/128)),((405/512),(1215/1024)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T294_ok T327_ok
def T292 : Node := Node.split 1 T293 T366
theorem T292_ok : Node.check D_R22222 T292 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T293_ok T366_ok
def T291 : Node := Node.leaf L291
theorem T291_ok : Node.check D_R22222 T291 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L291_ok
def T290 : Node := Node.split 3 T291 T292
theorem T290_ok : Node.check D_R22222 T290 [((163/256),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T291_ok T292_ok
def T289 : Node := Node.leaf L289
theorem T289_ok : Node.check D_R22222 T289 [((0),(163/256)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L289_ok
def T288 : Node := Node.split 0 T289 T290
theorem T288_ok : Node.check D_R22222 T288 [((0),(163/128)),((405/512),(405/256)),((405/256),(1215/512)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T289_ok T290_ok
def T287 : Node := Node.split 2 T288 T367
theorem T287_ok : Node.check D_R22222 T287 [((0),(163/128)),((405/512),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T288_ok T367_ok
def T286 : Node := Node.leaf L286
theorem T286_ok : Node.check D_R22222 T286 [((0),(163/128)),((0),(405/512)),((405/256),(405/128)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L286_ok
def T285 : Node := Node.split 1 T286 T287
theorem T285_ok : Node.check D_R22222 T285 [((0),(163/128)),((0),(405/256)),((405/256),(405/128)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T286_ok T287_ok
def T284 : Node := Node.split 3 T285 T410
theorem T284_ok : Node.check D_R22222 T284 [((0),(163/128)),((0),(405/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T285_ok T410_ok
def T283 : Node := Node.split 0 T284 T513
theorem T283_ok : Node.check D_R22222 T283 [((0),(163/64)),((0),(405/256)),((405/256),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T284_ok T513_ok
def T282 : Node := Node.leaf L282
theorem T282_ok : Node.check D_R22222 T282 [((489/256),(163/64)),((1215/1024),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L282_ok
def T281 : Node := Node.leaf L281
theorem T281_ok : Node.check D_R22222 T281 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L281_ok
def T280 : Node := Node.leaf L280
theorem T280_ok : Node.check D_R22222 T280 [((1141/512),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L280_ok
def T279 : Node := Node.leaf L279
theorem T279_ok : Node.check D_R22222 T279 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L279_ok
def T278 : Node := Node.leaf L278
theorem T278_ok : Node.check D_R22222 T278 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L278_ok
def T277 : Node := Node.leaf L277
theorem T277_ok : Node.check D_R22222 T277 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L277_ok
def T276 : Node := Node.leaf L276
theorem T276_ok : Node.check D_R22222 T276 [((4401/2048),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L276_ok
def T275 : Node := Node.leaf L275
theorem T275_ok : Node.check D_R22222 T275 [((2119/1024),(4401/2048)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L275_ok
def T274 : Node := Node.split 0 T275 T276
theorem T274_ok : Node.check D_R22222 T274 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T275_ok T276_ok
def T273 : Node := Node.split 2 T274 T277
theorem T273_ok : Node.check D_R22222 T273 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T274_ok T277_ok
def T272 : Node := Node.split 1 T273 T278
theorem T272_ok : Node.check D_R22222 T272 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T273_ok T278_ok
def T271 : Node := Node.leaf L271
theorem T271_ok : Node.check D_R22222 T271 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L271_ok
def T270 : Node := Node.leaf L270
theorem T270_ok : Node.check D_R22222 T270 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L270_ok
def T269 : Node := Node.leaf L269
theorem T269_ok : Node.check D_R22222 T269 [((4401/2048),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L269_ok
def T268 : Node := Node.leaf L268
theorem T268_ok : Node.check D_R22222 T268 [((2119/1024),(4401/2048)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L268_ok
def T267 : Node := Node.split 0 T268 T269
theorem T267_ok : Node.check D_R22222 T267 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T268_ok T269_ok
def T266 : Node := Node.split 2 T267 T270
theorem T266_ok : Node.check D_R22222 T266 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T267_ok T270_ok
def T265 : Node := Node.split 1 T266 T271
theorem T265_ok : Node.check D_R22222 T265 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T266_ok T271_ok
def T264 : Node := Node.split 3 T265 T272
theorem T264_ok : Node.check D_R22222 T264 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T265_ok T272_ok
def T263 : Node := Node.leaf L263
theorem T263_ok : Node.check D_R22222 T263 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L263_ok
def T262 : Node := Node.leaf L262
theorem T262_ok : Node.check D_R22222 T262 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L262_ok
def T261 : Node := Node.split 2 T262 T263
theorem T261_ok : Node.check D_R22222 T261 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T262_ok T263_ok
def T260 : Node := Node.leaf L260
theorem T260_ok : Node.check D_R22222 T260 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L260_ok
def T259 : Node := Node.leaf L259
theorem T259_ok : Node.check D_R22222 T259 [((4075/2048),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L259_ok
def T258 : Node := Node.leaf L258
theorem T258_ok : Node.check D_R22222 T258 [((489/256),(4075/2048)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L258_ok
def T257 : Node := Node.split 0 T258 T259
theorem T257_ok : Node.check D_R22222 T257 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T258_ok T259_ok
def T256 : Node := Node.split 2 T257 T260
theorem T256_ok : Node.check D_R22222 T256 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T257_ok T260_ok
def T255 : Node := Node.split 1 T256 T261
theorem T255_ok : Node.check D_R22222 T255 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T256_ok T261_ok
def T254 : Node := Node.leaf L254
theorem T254_ok : Node.check D_R22222 T254 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L254_ok
def T253 : Node := Node.leaf L253
theorem T253_ok : Node.check D_R22222 T253 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L253_ok
def T252 : Node := Node.split 2 T253 T254
theorem T252_ok : Node.check D_R22222 T252 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T253_ok T254_ok
def T251 : Node := Node.leaf L251
theorem T251_ok : Node.check D_R22222 T251 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L251_ok
def T250 : Node := Node.leaf L250
theorem T250_ok : Node.check D_R22222 T250 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L250_ok
def T249 : Node := Node.split 2 T250 T251
theorem T249_ok : Node.check D_R22222 T249 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T250_ok T251_ok
def T248 : Node := Node.split 1 T249 T252
theorem T248_ok : Node.check D_R22222 T248 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T249_ok T252_ok
def T247 : Node := Node.split 3 T248 T255
theorem T247_ok : Node.check D_R22222 T247 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T248_ok T255_ok
def T246 : Node := Node.split 0 T247 T264
theorem T246_ok : Node.check D_R22222 T246 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T247_ok T264_ok
def T245 : Node := Node.leaf L245
theorem T245_ok : Node.check D_R22222 T245 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L245_ok
def T244 : Node := Node.split 2 T245 T246
theorem T244_ok : Node.check D_R22222 T244 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T245_ok T246_ok
def T243 : Node := Node.leaf L243
theorem T243_ok : Node.check D_R22222 T243 [((489/256),(1141/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L243_ok
def T242 : Node := Node.split 1 T243 T244
theorem T242_ok : Node.check D_R22222 T242 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T243_ok T244_ok
def T241 : Node := Node.split 3 T242 T279
theorem T241_ok : Node.check D_R22222 T241 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T242_ok T279_ok
def T240 : Node := Node.split 0 T241 T280
theorem T240_ok : Node.check D_R22222 T240 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T241_ok T280_ok
def T239 : Node := Node.split 2 T240 T281
theorem T239_ok : Node.check D_R22222 T239 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T240_ok T281_ok
def T238 : Node := Node.split 1 T239 T282
theorem T238_ok : Node.check D_R22222 T238 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T239_ok T282_ok
def T237 : Node := Node.leaf L237
theorem T237_ok : Node.check D_R22222 T237 [((489/256),(163/64)),((1215/1024),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L237_ok
def T236 : Node := Node.leaf L236
theorem T236_ok : Node.check D_R22222 T236 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L236_ok
def T235 : Node := Node.leaf L235
theorem T235_ok : Node.check D_R22222 T235 [((1141/512),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L235_ok
def T234 : Node := Node.leaf L234
theorem T234_ok : Node.check D_R22222 T234 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1793/1024),(489/256))] = true := Node.check_leaf_of _ _ _ L234_ok
def T233 : Node := Node.leaf L233
theorem T233_ok : Node.check D_R22222 T233 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/512),(1793/1024))] = true := Node.check_leaf_of _ _ _ L233_ok
def T232 : Node := Node.split 3 T233 T234
theorem T232_ok : Node.check D_R22222 T232 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/512),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T233_ok T234_ok
def T231 : Node := Node.leaf L231
theorem T231_ok : Node.check D_R22222 T231 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1793/1024),(489/256))] = true := Node.check_leaf_of _ _ _ L231_ok
def T230 : Node := Node.leaf L230
theorem T230_ok : Node.check D_R22222 T230 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/512),(1793/1024))] = true := Node.check_leaf_of _ _ _ L230_ok
def T229 : Node := Node.split 3 T230 T231
theorem T229_ok : Node.check D_R22222 T229 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/512),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T230_ok T231_ok
def T228 : Node := Node.split 0 T229 T232
theorem T228_ok : Node.check D_R22222 T228 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/512),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T229_ok T232_ok
def T227 : Node := Node.leaf L227
theorem T227_ok : Node.check D_R22222 T227 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((815/512),(489/256))] = true := Node.check_leaf_of _ _ _ L227_ok
def T226 : Node := Node.split 2 T227 T228
theorem T226_ok : Node.check D_R22222 T226 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((815/512),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T227_ok T228_ok
def T225 : Node := Node.leaf L225
theorem T225_ok : Node.check D_R22222 T225 [((489/256),(1141/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((815/512),(489/256))] = true := Node.check_leaf_of _ _ _ L225_ok
def T224 : Node := Node.split 1 T225 T226
theorem T224_ok : Node.check D_R22222 T224 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/512),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T225_ok T226_ok
def T223 : Node := Node.leaf L223
theorem T223_ok : Node.check D_R22222 T223 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(815/512))] = true := Node.check_leaf_of _ _ _ L223_ok
def T222 : Node := Node.split 3 T223 T224
theorem T222_ok : Node.check D_R22222 T222 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T223_ok T224_ok
def T221 : Node := Node.split 0 T222 T235
theorem T221_ok : Node.check D_R22222 T221 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T222_ok T235_ok
def T220 : Node := Node.split 2 T221 T236
theorem T220_ok : Node.check D_R22222 T220 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T221_ok T236_ok
def T219 : Node := Node.split 1 T220 T237
theorem T219_ok : Node.check D_R22222 T219 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T220_ok T237_ok
def T218 : Node := Node.split 3 T219 T238
theorem T218_ok : Node.check D_R22222 T218 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T219_ok T238_ok
def T217 : Node := Node.leaf L217
theorem T217_ok : Node.check D_R22222 T217 [((163/128),(489/256)),((1215/1024),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L217_ok
def T216 : Node := Node.leaf L216
theorem T216_ok : Node.check D_R22222 T216 [((163/128),(489/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L216_ok
def T215 : Node := Node.leaf L215
theorem T215_ok : Node.check D_R22222 T215 [((815/512),(489/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L215_ok
def T214 : Node := Node.leaf L214
theorem T214_ok : Node.check D_R22222 T214 [((1793/1024),(489/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L214_ok
def T213 : Node := Node.leaf L213
theorem T213_ok : Node.check D_R22222 T213 [((815/512),(1793/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L213_ok
def T212 : Node := Node.split 0 T213 T214
theorem T212_ok : Node.check D_R22222 T212 [((815/512),(489/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T213_ok T214_ok
def T211 : Node := Node.leaf L211
theorem T211_ok : Node.check D_R22222 T211 [((815/512),(489/256)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L211_ok
def T210 : Node := Node.split 2 T211 T212
theorem T210_ok : Node.check D_R22222 T210 [((815/512),(489/256)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T211_ok T212_ok
def T209 : Node := Node.leaf L209
theorem T209_ok : Node.check D_R22222 T209 [((815/512),(489/256)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L209_ok
def T208 : Node := Node.split 1 T209 T210
theorem T208_ok : Node.check D_R22222 T208 [((815/512),(489/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T209_ok T210_ok
def T207 : Node := Node.split 3 T208 T215
theorem T207_ok : Node.check D_R22222 T207 [((815/512),(489/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T208_ok T215_ok
def T206 : Node := Node.leaf L206
theorem T206_ok : Node.check D_R22222 T206 [((163/128),(815/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L206_ok
def T205 : Node := Node.split 0 T206 T207
theorem T205_ok : Node.check D_R22222 T205 [((163/128),(489/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T206_ok T207_ok
def T204 : Node := Node.split 2 T205 T216
theorem T204_ok : Node.check D_R22222 T204 [((163/128),(489/256)),((405/512),(1215/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T205_ok T216_ok
def T203 : Node := Node.split 1 T204 T217
theorem T203_ok : Node.check D_R22222 T203 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T204_ok T217_ok
def T202 : Node := Node.leaf L202
theorem T202_ok : Node.check D_R22222 T202 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L202_ok
def T201 : Node := Node.split 3 T202 T203
theorem T201_ok : Node.check D_R22222 T201 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T202_ok T203_ok
def T200 : Node := Node.split 0 T201 T218
theorem T200_ok : Node.check D_R22222 T200 [((163/128),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T201_ok T218_ok
def T199 : Node := Node.leaf L199
theorem T199_ok : Node.check D_R22222 T199 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L199_ok
def T198 : Node := Node.split 2 T199 T200
theorem T198_ok : Node.check D_R22222 T198 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T199_ok T200_ok
def T197 : Node := Node.leaf L197
theorem T197_ok : Node.check D_R22222 T197 [((163/128),(163/64)),((0),(405/512)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L197_ok
def T196 : Node := Node.split 1 T197 T198
theorem T196_ok : Node.check D_R22222 T196 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T197_ok T198_ok
def T195 : Node := Node.leaf L195
theorem T195_ok : Node.check D_R22222 T195 [((489/256),(163/64)),((1215/1024),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L195_ok
def T194 : Node := Node.leaf L194
theorem T194_ok : Node.check D_R22222 T194 [((489/256),(163/64)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L194_ok
def T193 : Node := Node.leaf L193
theorem T193_ok : Node.check D_R22222 T193 [((1141/512),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L193_ok
def T192 : Node := Node.leaf L192
theorem T192_ok : Node.check D_R22222 T192 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L192_ok
def T191 : Node := Node.leaf L191
theorem T191_ok : Node.check D_R22222 T191 [((2119/1024),(1141/512)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L191_ok
def T190 : Node := Node.leaf L190
theorem T190_ok : Node.check D_R22222 T190 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L190_ok
def T189 : Node := Node.leaf L189
theorem T189_ok : Node.check D_R22222 T189 [((4401/2048),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L189_ok
def T188 : Node := Node.leaf L188
theorem T188_ok : Node.check D_R22222 T188 [((2119/1024),(4401/2048)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L188_ok
def T187 : Node := Node.split 0 T188 T189
theorem T187_ok : Node.check D_R22222 T187 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T188_ok T189_ok
def T186 : Node := Node.split 2 T187 T190
theorem T186_ok : Node.check D_R22222 T186 [((2119/1024),(1141/512)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T187_ok T190_ok
def T185 : Node := Node.split 1 T186 T191
theorem T185_ok : Node.check D_R22222 T185 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T186_ok T191_ok
def T184 : Node := Node.split 3 T185 T192
theorem T184_ok : Node.check D_R22222 T184 [((2119/1024),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T185_ok T192_ok
def T183 : Node := Node.leaf L183
theorem T183_ok : Node.check D_R22222 T183 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L183_ok
def T182 : Node := Node.leaf L182
theorem T182_ok : Node.check D_R22222 T182 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L182_ok
def T181 : Node := Node.leaf L181
theorem T181_ok : Node.check D_R22222 T181 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L181_ok
def T180 : Node := Node.split 2 T181 T182
theorem T180_ok : Node.check D_R22222 T180 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T181_ok T182_ok
def T179 : Node := Node.split 1 T180 T183
theorem T179_ok : Node.check D_R22222 T179 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T180_ok T183_ok
def T178 : Node := Node.leaf L178
theorem T178_ok : Node.check D_R22222 T178 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L178_ok
def T177 : Node := Node.leaf L177
theorem T177_ok : Node.check D_R22222 T177 [((4075/2048),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L177_ok
def T176 : Node := Node.leaf L176
theorem T176_ok : Node.check D_R22222 T176 [((489/256),(4075/2048)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L176_ok
def T175 : Node := Node.split 0 T176 T177
theorem T175_ok : Node.check D_R22222 T175 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T176_ok T177_ok
def T174 : Node := Node.split 2 T175 T178
theorem T174_ok : Node.check D_R22222 T174 [((489/256),(2119/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T175_ok T178_ok
def T173 : Node := Node.leaf L173
theorem T173_ok : Node.check D_R22222 T173 [((4075/2048),(2119/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L173_ok
def T172 : Node := Node.leaf L172
theorem T172_ok : Node.check D_R22222 T172 [((489/256),(4075/2048)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L172_ok
def T171 : Node := Node.split 0 T172 T173
theorem T171_ok : Node.check D_R22222 T171 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T172_ok T173_ok
def T170 : Node := Node.leaf L170
theorem T170_ok : Node.check D_R22222 T170 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L170_ok
def T169 : Node := Node.split 2 T170 T171
theorem T169_ok : Node.check D_R22222 T169 [((489/256),(2119/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T170_ok T171_ok
def T168 : Node := Node.split 1 T169 T174
theorem T168_ok : Node.check D_R22222 T168 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T169_ok T174_ok
def T167 : Node := Node.split 3 T168 T179
theorem T167_ok : Node.check D_R22222 T167 [((489/256),(2119/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T168_ok T179_ok
def T166 : Node := Node.split 0 T167 T184
theorem T166_ok : Node.check D_R22222 T166 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T167_ok T184_ok
def T165 : Node := Node.leaf L165
theorem T165_ok : Node.check D_R22222 T165 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L165_ok
def T164 : Node := Node.split 2 T165 T166
theorem T164_ok : Node.check D_R22222 T164 [((489/256),(1141/512)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T165_ok T166_ok
def T163 : Node := Node.leaf L163
theorem T163_ok : Node.check D_R22222 T163 [((489/256),(1141/512)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L163_ok
def T162 : Node := Node.split 1 T163 T164
theorem T162_ok : Node.check D_R22222 T162 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T163_ok T164_ok
def T161 : Node := Node.leaf L161
theorem T161_ok : Node.check D_R22222 T161 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L161_ok
def T160 : Node := Node.split 3 T161 T162
theorem T160_ok : Node.check D_R22222 T160 [((489/256),(1141/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T161_ok T162_ok
def T159 : Node := Node.split 0 T160 T193
theorem T159_ok : Node.check D_R22222 T159 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T160_ok T193_ok
def T158 : Node := Node.split 2 T159 T194
theorem T158_ok : Node.check D_R22222 T158 [((489/256),(163/64)),((405/512),(1215/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T159_ok T194_ok
def T157 : Node := Node.split 1 T158 T195
theorem T157_ok : Node.check D_R22222 T157 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T158_ok T195_ok
def T156 : Node := Node.leaf L156
theorem T156_ok : Node.check D_R22222 T156 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L156_ok
def T155 : Node := Node.split 3 T156 T157
theorem T155_ok : Node.check D_R22222 T155 [((489/256),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T156_ok T157_ok
def T154 : Node := Node.leaf L154
theorem T154_ok : Node.check D_R22222 T154 [((163/128),(489/256)),((1215/1024),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L154_ok
def T153 : Node := Node.leaf L153
theorem T153_ok : Node.check D_R22222 T153 [((163/128),(489/256)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L153_ok
def T152 : Node := Node.leaf L152
theorem T152_ok : Node.check D_R22222 T152 [((1793/1024),(489/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L152_ok
def T151 : Node := Node.leaf L151
theorem T151_ok : Node.check D_R22222 T151 [((1793/1024),(489/256)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L151_ok
def T150 : Node := Node.leaf L150
theorem T150_ok : Node.check D_R22222 T150 [((1793/1024),(489/256)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L150_ok
def T149 : Node := Node.split 2 T150 T151
theorem T149_ok : Node.check D_R22222 T149 [((1793/1024),(489/256)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T150_ok T151_ok
def T148 : Node := Node.leaf L148
theorem T148_ok : Node.check D_R22222 T148 [((1793/1024),(489/256)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L148_ok
def T147 : Node := Node.leaf L147
theorem T147_ok : Node.check D_R22222 T147 [((1793/1024),(489/256)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L147_ok
def T146 : Node := Node.split 2 T147 T148
theorem T146_ok : Node.check D_R22222 T146 [((1793/1024),(489/256)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T147_ok T148_ok
def T145 : Node := Node.split 1 T146 T149
theorem T145_ok : Node.check D_R22222 T145 [((1793/1024),(489/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T146_ok T149_ok
def T144 : Node := Node.split 3 T145 T152
theorem T144_ok : Node.check D_R22222 T144 [((1793/1024),(489/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T145_ok T152_ok
def T143 : Node := Node.leaf L143
theorem T143_ok : Node.check D_R22222 T143 [((815/512),(1793/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L143_ok
def T142 : Node := Node.split 0 T143 T144
theorem T142_ok : Node.check D_R22222 T142 [((815/512),(489/256)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T143_ok T144_ok
def T141 : Node := Node.leaf L141
theorem T141_ok : Node.check D_R22222 T141 [((815/512),(489/256)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L141_ok
def T140 : Node := Node.split 2 T141 T142
theorem T140_ok : Node.check D_R22222 T140 [((815/512),(489/256)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T141_ok T142_ok
def T139 : Node := Node.leaf L139
theorem T139_ok : Node.check D_R22222 T139 [((815/512),(489/256)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L139_ok
def T138 : Node := Node.split 1 T139 T140
theorem T138_ok : Node.check D_R22222 T138 [((815/512),(489/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T139_ok T140_ok
def T137 : Node := Node.leaf L137
theorem T137_ok : Node.check D_R22222 T137 [((815/512),(489/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L137_ok
def T136 : Node := Node.split 3 T137 T138
theorem T136_ok : Node.check D_R22222 T136 [((815/512),(489/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T137_ok T138_ok
def T135 : Node := Node.leaf L135
theorem T135_ok : Node.check D_R22222 T135 [((163/128),(815/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L135_ok
def T134 : Node := Node.split 0 T135 T136
theorem T134_ok : Node.check D_R22222 T134 [((163/128),(489/256)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T135_ok T136_ok
def T133 : Node := Node.split 2 T134 T153
theorem T133_ok : Node.check D_R22222 T133 [((163/128),(489/256)),((405/512),(1215/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T134_ok T153_ok
def T132 : Node := Node.split 1 T133 T154
theorem T132_ok : Node.check D_R22222 T132 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T133_ok T154_ok
def T131 : Node := Node.leaf L131
theorem T131_ok : Node.check D_R22222 T131 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L131_ok
def T130 : Node := Node.split 3 T131 T132
theorem T130_ok : Node.check D_R22222 T130 [((163/128),(489/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T131_ok T132_ok
def T129 : Node := Node.split 0 T130 T155
theorem T129_ok : Node.check D_R22222 T129 [((163/128),(163/64)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T130_ok T155_ok
def T128 : Node := Node.leaf L128
theorem T128_ok : Node.check D_R22222 T128 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L128_ok
def T127 : Node := Node.split 2 T128 T129
theorem T127_ok : Node.check D_R22222 T127 [((163/128),(163/64)),((405/512),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T128_ok T129_ok
def T126 : Node := Node.leaf L126
theorem T126_ok : Node.check D_R22222 T126 [((163/128),(163/64)),((0),(405/512)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L126_ok
def T125 : Node := Node.split 1 T126 T127
theorem T125_ok : Node.check D_R22222 T125 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T126_ok T127_ok
def T124 : Node := Node.split 3 T125 T196
theorem T124_ok : Node.check D_R22222 T124 [((163/128),(163/64)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T125_ok T196_ok
def T123 : Node := Node.leaf L123
theorem T123_ok : Node.check D_R22222 T123 [((163/256),(163/128)),((1215/1024),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L123_ok
def T122 : Node := Node.leaf L122
theorem T122_ok : Node.check D_R22222 T122 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L122_ok
def T121 : Node := Node.leaf L121
theorem T121_ok : Node.check D_R22222 T121 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((1141/512),(163/64))] = true := Node.check_leaf_of _ _ _ L121_ok
def T120 : Node := Node.leaf L120
theorem T120_ok : Node.check D_R22222 T120 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L120_ok
def T119 : Node := Node.leaf L119
theorem T119_ok : Node.check D_R22222 T119 [((1141/1024),(163/128)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L119_ok
def T118 : Node := Node.leaf L118
theorem T118_ok : Node.check D_R22222 T118 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L118_ok
def T117 : Node := Node.leaf L117
theorem T117_ok : Node.check D_R22222 T117 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L117_ok
def T116 : Node := Node.split 2 T117 T118
theorem T116_ok : Node.check D_R22222 T116 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T117_ok T118_ok
def T115 : Node := Node.split 1 T116 T119
theorem T115_ok : Node.check D_R22222 T115 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T116_ok T119_ok
def T114 : Node := Node.split 3 T115 T120
theorem T114_ok : Node.check D_R22222 T114 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T115_ok T120_ok
def T113 : Node := Node.leaf L113
theorem T113_ok : Node.check D_R22222 T113 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L113_ok
def T112 : Node := Node.leaf L112
theorem T112_ok : Node.check D_R22222 T112 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L112_ok
def T111 : Node := Node.split 2 T112 T113
theorem T111_ok : Node.check D_R22222 T111 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T112_ok T113_ok
def T110 : Node := Node.leaf L110
theorem T110_ok : Node.check D_R22222 T110 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L110_ok
def T109 : Node := Node.leaf L109
theorem T109_ok : Node.check D_R22222 T109 [((2119/2048),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L109_ok
def T108 : Node := Node.leaf L108
theorem T108_ok : Node.check D_R22222 T108 [((489/512),(2119/2048)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true := Node.check_leaf_of _ _ _ L108_ok
def T107 : Node := Node.split 0 T108 T109
theorem T107_ok : Node.check D_R22222 T107 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T108_ok T109_ok
def T106 : Node := Node.split 2 T107 T110
theorem T106_ok : Node.check D_R22222 T106 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T107_ok T110_ok
def T105 : Node := Node.split 1 T106 T111
theorem T105_ok : Node.check D_R22222 T105 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((2119/1024),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T106_ok T111_ok
def T104 : Node := Node.leaf L104
theorem T104_ok : Node.check D_R22222 T104 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L104_ok
def T103 : Node := Node.leaf L103
theorem T103_ok : Node.check D_R22222 T103 [((2119/2048),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L103_ok
def T102 : Node := Node.leaf L102
theorem T102_ok : Node.check D_R22222 T102 [((489/512),(2119/2048)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L102_ok
def T101 : Node := Node.split 0 T102 T103
theorem T101_ok : Node.check D_R22222 T101 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T102_ok T103_ok
def T100 : Node := Node.split 2 T101 T104
theorem T100_ok : Node.check D_R22222 T100 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T101_ok T104_ok
def T99 : Node := Node.leaf L99
theorem T99_ok : Node.check D_R22222 T99 [((2119/2048),(1141/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L99_ok
def T98 : Node := Node.leaf L98
theorem T98_ok : Node.check D_R22222 T98 [((489/512),(2119/2048)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L98_ok
def T97 : Node := Node.split 0 T98 T99
theorem T97_ok : Node.check D_R22222 T97 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T98_ok T99_ok
def T96 : Node := Node.leaf L96
theorem T96_ok : Node.check D_R22222 T96 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/256),(2119/1024))] = true := Node.check_leaf_of _ _ _ L96_ok
def T95 : Node := Node.split 2 T96 T97
theorem T95_ok : Node.check D_R22222 T95 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T96_ok T97_ok
def T94 : Node := Node.split 1 T95 T100
theorem T94_ok : Node.check D_R22222 T94 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(2119/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T95_ok T100_ok
def T93 : Node := Node.split 3 T94 T105
theorem T93_ok : Node.check D_R22222 T93 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T94_ok T105_ok
def T92 : Node := Node.split 0 T93 T114
theorem T92_ok : Node.check D_R22222 T92 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T93_ok T114_ok
def T91 : Node := Node.leaf L91
theorem T91_ok : Node.check D_R22222 T91 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L91_ok
def T90 : Node := Node.split 2 T91 T92
theorem T90_ok : Node.check D_R22222 T90 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T91_ok T92_ok
def T89 : Node := Node.leaf L89
theorem T89_ok : Node.check D_R22222 T89 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/256),(1141/512))] = true := Node.check_leaf_of _ _ _ L89_ok
def T88 : Node := Node.split 1 T89 T90
theorem T88_ok : Node.check D_R22222 T88 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(1141/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T89_ok T90_ok
def T87 : Node := Node.split 3 T88 T121
theorem T87_ok : Node.check D_R22222 T87 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T88_ok T121_ok
def T86 : Node := Node.leaf L86
theorem T86_ok : Node.check D_R22222 T86 [((163/256),(489/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true := Node.check_leaf_of _ _ _ L86_ok
def T85 : Node := Node.split 0 T86 T87
theorem T85_ok : Node.check D_R22222 T85 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T86_ok T87_ok
def T84 : Node := Node.split 2 T85 T122
theorem T84_ok : Node.check D_R22222 T84 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T85_ok T122_ok
def T83 : Node := Node.split 1 T84 T123
theorem T83_ok : Node.check D_R22222 T83 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((489/256),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T84_ok T123_ok
def T82 : Node := Node.leaf L82
theorem T82_ok : Node.check D_R22222 T82 [((163/256),(163/128)),((1215/1024),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L82_ok
def T81 : Node := Node.leaf L81
theorem T81_ok : Node.check D_R22222 T81 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L81_ok
def T80 : Node := Node.leaf L80
theorem T80_ok : Node.check D_R22222 T80 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/512),(489/256))] = true := Node.check_leaf_of _ _ _ L80_ok
def T79 : Node := Node.leaf L79
theorem T79_ok : Node.check D_R22222 T79 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((1793/1024),(489/256))] = true := Node.check_leaf_of _ _ _ L79_ok
def T78 : Node := Node.leaf L78
theorem T78_ok : Node.check D_R22222 T78 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((1793/1024),(489/256))] = true := Node.check_leaf_of _ _ _ L78_ok
def T77 : Node := Node.split 1 T78 T79
theorem T77_ok : Node.check D_R22222 T77 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1793/1024),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T78_ok T79_ok
def T76 : Node := Node.leaf L76
theorem T76_ok : Node.check D_R22222 T76 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/512),(1793/1024))] = true := Node.check_leaf_of _ _ _ L76_ok
def T75 : Node := Node.split 3 T76 T77
theorem T75_ok : Node.check D_R22222 T75 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/512),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T76_ok T77_ok
def T74 : Node := Node.split 0 T75 T80
theorem T74_ok : Node.check D_R22222 T74 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((815/512),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T75_ok T80_ok
def T73 : Node := Node.leaf L73
theorem T73_ok : Node.check D_R22222 T73 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((815/512),(489/256))] = true := Node.check_leaf_of _ _ _ L73_ok
def T72 : Node := Node.split 2 T73 T74
theorem T72_ok : Node.check D_R22222 T72 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((815/512),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T73_ok T74_ok
def T71 : Node := Node.leaf L71
theorem T71_ok : Node.check D_R22222 T71 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((815/512),(489/256))] = true := Node.check_leaf_of _ _ _ L71_ok
def T70 : Node := Node.split 1 T71 T72
theorem T70_ok : Node.check D_R22222 T70 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((815/512),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T71_ok T72_ok
def T69 : Node := Node.leaf L69
theorem T69_ok : Node.check D_R22222 T69 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(815/512))] = true := Node.check_leaf_of _ _ _ L69_ok
def T68 : Node := Node.split 3 T69 T70
theorem T68_ok : Node.check D_R22222 T68 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T69_ok T70_ok
def T67 : Node := Node.leaf L67
theorem T67_ok : Node.check D_R22222 T67 [((163/256),(489/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(489/256))] = true := Node.check_leaf_of _ _ _ L67_ok
def T66 : Node := Node.split 0 T67 T68
theorem T66_ok : Node.check D_R22222 T66 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T67_ok T68_ok
def T65 : Node := Node.split 2 T66 T81
theorem T65_ok : Node.check D_R22222 T65 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T66_ok T81_ok
def T64 : Node := Node.split 1 T65 T82
theorem T64_ok : Node.check D_R22222 T64 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(489/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T65_ok T82_ok
def T63 : Node := Node.split 3 T64 T83
theorem T63_ok : Node.check D_R22222 T63 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T64_ok T83_ok
def T62 : Node := Node.leaf L62
theorem T62_ok : Node.check D_R22222 T62 [((0),(163/256)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L62_ok
def T61 : Node := Node.split 0 T62 T63
theorem T61_ok : Node.check D_R22222 T61 [((0),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T62_ok T63_ok
def T60 : Node := Node.leaf L60
theorem T60_ok : Node.check D_R22222 T60 [((0),(163/128)),((405/512),(405/256)),((0),(405/512)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L60_ok
def T59 : Node := Node.split 2 T60 T61
theorem T59_ok : Node.check D_R22222 T59 [((0),(163/128)),((405/512),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T60_ok T61_ok
def T58 : Node := Node.leaf L58
theorem T58_ok : Node.check D_R22222 T58 [((0),(163/128)),((0),(405/512)),((0),(405/256)),((163/128),(163/64))] = true := Node.check_leaf_of _ _ _ L58_ok
def T57 : Node := Node.split 1 T58 T59
theorem T57_ok : Node.check D_R22222 T57 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((163/128),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T58_ok T59_ok
def T56 : Node := Node.leaf L56
theorem T56_ok : Node.check D_R22222 T56 [((163/256),(163/128)),((1215/1024),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L56_ok
def T55 : Node := Node.leaf L55
theorem T55_ok : Node.check D_R22222 T55 [((163/256),(163/128)),((405/512),(1215/1024)),((1215/1024),(405/256)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L55_ok
def T54 : Node := Node.leaf L54
theorem T54_ok : Node.check D_R22222 T54 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L54_ok
def T53 : Node := Node.leaf L53
theorem T53_ok : Node.check D_R22222 T53 [((1141/1024),(163/128)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L53_ok
def T52 : Node := Node.leaf L52
theorem T52_ok : Node.check D_R22222 T52 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L52_ok
def T51 : Node := Node.leaf L51
theorem T51_ok : Node.check D_R22222 T51 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L51_ok
def T50 : Node := Node.split 2 T51 T52
theorem T50_ok : Node.check D_R22222 T50 [((1141/1024),(163/128)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T51_ok T52_ok
def T49 : Node := Node.split 1 T50 T53
theorem T49_ok : Node.check D_R22222 T49 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T50_ok T53_ok
def T48 : Node := Node.split 3 T49 T54
theorem T48_ok : Node.check D_R22222 T48 [((1141/1024),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T49_ok T54_ok
def T47 : Node := Node.leaf L47
theorem T47_ok : Node.check D_R22222 T47 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L47_ok
def T46 : Node := Node.leaf L46
theorem T46_ok : Node.check D_R22222 T46 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L46_ok
def T45 : Node := Node.leaf L45
theorem T45_ok : Node.check D_R22222 T45 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((1141/1024),(163/128))] = true := Node.check_leaf_of _ _ _ L45_ok
def T44 : Node := Node.split 2 T45 T46
theorem T44_ok : Node.check D_R22222 T44 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T45_ok T46_ok
def T43 : Node := Node.split 1 T44 T47
theorem T43_ok : Node.check D_R22222 T43 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((1141/1024),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T44_ok T47_ok
def T42 : Node := Node.leaf L42
theorem T42_ok : Node.check D_R22222 T42 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L42_ok
def T41 : Node := Node.leaf L41
theorem T41_ok : Node.check D_R22222 T41 [((2119/2048),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L41_ok
def T40 : Node := Node.leaf L40
theorem T40_ok : Node.check D_R22222 T40 [((489/512),(2119/2048)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L40_ok
def T39 : Node := Node.split 0 T40 T41
theorem T39_ok : Node.check D_R22222 T39 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T40_ok T41_ok
def T38 : Node := Node.split 2 T39 T42
theorem T38_ok : Node.check D_R22222 T38 [((489/512),(1141/1024)),((4455/4096),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T39_ok T42_ok
def T37 : Node := Node.leaf L37
theorem T37_ok : Node.check D_R22222 T37 [((2119/2048),(1141/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L37_ok
def T36 : Node := Node.leaf L36
theorem T36_ok : Node.check D_R22222 T36 [((489/512),(2119/2048)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L36_ok
def T35 : Node := Node.split 0 T36 T37
theorem T35_ok : Node.check D_R22222 T35 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((4455/4096),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T36_ok T37_ok
def T34 : Node := Node.leaf L34
theorem T34_ok : Node.check D_R22222 T34 [((2119/2048),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L34_ok
def T33 : Node := Node.leaf L33
theorem T33_ok : Node.check D_R22222 T33 [((489/512),(2119/2048)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true := Node.check_leaf_of _ _ _ L33_ok
def T32 : Node := Node.split 0 T33 T34
theorem T32_ok : Node.check D_R22222 T32 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(4455/4096)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T33_ok T34_ok
def T31 : Node := Node.split 2 T32 T35
theorem T31_ok : Node.check D_R22222 T31 [((489/512),(1141/1024)),((2025/2048),(4455/4096)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T32_ok T35_ok
def T30 : Node := Node.split 1 T31 T38
theorem T30_ok : Node.check D_R22222 T30 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(1141/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T31_ok T38_ok
def T29 : Node := Node.split 3 T30 T43
theorem T29_ok : Node.check D_R22222 T29 [((489/512),(1141/1024)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T30_ok T43_ok
def T28 : Node := Node.split 0 T29 T48
theorem T28_ok : Node.check D_R22222 T28 [((489/512),(163/128)),((2025/2048),(1215/1024)),((2025/2048),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T29_ok T48_ok
def T27 : Node := Node.leaf L27
theorem T27_ok : Node.check D_R22222 T27 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(2025/2048)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L27_ok
def T26 : Node := Node.split 2 T27 T28
theorem T26_ok : Node.check D_R22222 T26 [((489/512),(163/128)),((2025/2048),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T27_ok T28_ok
def T25 : Node := Node.leaf L25
theorem T25_ok : Node.check D_R22222 T25 [((489/512),(163/128)),((405/512),(2025/2048)),((405/512),(1215/1024)),((489/512),(163/128))] = true := Node.check_leaf_of _ _ _ L25_ok
def T24 : Node := Node.split 1 T25 T26
theorem T24_ok : Node.check D_R22222 T24 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((489/512),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T25_ok T26_ok
def T23 : Node := Node.leaf L23
theorem T23_ok : Node.check D_R22222 T23 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(489/512))] = true := Node.check_leaf_of _ _ _ L23_ok
def T22 : Node := Node.split 3 T23 T24
theorem T22_ok : Node.check D_R22222 T22 [((489/512),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T23_ok T24_ok
def T21 : Node := Node.leaf L21
theorem T21_ok : Node.check D_R22222 T21 [((163/256),(489/512)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true := Node.check_leaf_of _ _ _ L21_ok
def T20 : Node := Node.split 0 T21 T22
theorem T20_ok : Node.check D_R22222 T20 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(1215/1024)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T21_ok T22_ok
def T19 : Node := Node.split 2 T20 T55
theorem T19_ok : Node.check D_R22222 T19 [((163/256),(163/128)),((405/512),(1215/1024)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T20_ok T55_ok
def T18 : Node := Node.split 1 T19 T56
theorem T18_ok : Node.check D_R22222 T18 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((163/256),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T19_ok T56_ok
def T17 : Node := Node.leaf L17
theorem T17_ok : Node.check D_R22222 T17 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/256))] = true := Node.check_leaf_of _ _ _ L17_ok
def T16 : Node := Node.split 3 T17 T18
theorem T16_ok : Node.check D_R22222 T16 [((163/256),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T17_ok T18_ok
def T15 : Node := Node.leaf L15
theorem T15_ok : Node.check D_R22222 T15 [((0),(163/256)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L15_ok
def T14 : Node := Node.split 0 T15 T16
theorem T14_ok : Node.check D_R22222 T14 [((0),(163/128)),((405/512),(405/256)),((405/512),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T15_ok T16_ok
def T13 : Node := Node.leaf L13
theorem T13_ok : Node.check D_R22222 T13 [((0),(163/128)),((405/512),(405/256)),((0),(405/512)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L13_ok
def T12 : Node := Node.split 2 T13 T14
theorem T12_ok : Node.check D_R22222 T12 [((0),(163/128)),((405/512),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T13_ok T14_ok
def T11 : Node := Node.leaf L11
theorem T11_ok : Node.check D_R22222 T11 [((0),(163/128)),((0),(405/512)),((0),(405/256)),((0),(163/128))] = true := Node.check_leaf_of _ _ _ L11_ok
def T10 : Node := Node.split 1 T11 T12
theorem T10_ok : Node.check D_R22222 T10 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((0),(163/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T11_ok T12_ok
def T9 : Node := Node.split 3 T10 T57
theorem T9_ok : Node.check D_R22222 T9 [((0),(163/128)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T10_ok T57_ok
def T8 : Node := Node.split 0 T9 T124
theorem T8_ok : Node.check D_R22222 T8 [((0),(163/64)),((0),(405/256)),((0),(405/256)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T9_ok T124_ok
def T7 : Node := Node.split 2 T8 T283
theorem T7_ok : Node.check D_R22222 T7 [((0),(163/64)),((0),(405/256)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T8_ok T283_ok
def T6 : Node := Node.split 1 T7 T742
theorem T6_ok : Node.check D_R22222 T6 [((0),(163/64)),((0),(405/128)),((0),(405/128)),((0),(163/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T7_ok T742_ok
def T5 : Node := Node.split 3 T6 T1557
theorem T5_ok : Node.check D_R22222 T5 [((0),(163/64)),((0),(405/128)),((0),(405/128)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T6_ok T1557_ok
def T4 : Node := Node.split 0 T5 T2222
theorem T4_ok : Node.check D_R22222 T4 [((0),(163/32)),((0),(405/128)),((0),(405/128)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T5_ok T2222_ok
def T3 : Node := Node.split 2 T4 T3145
theorem T3_ok : Node.check D_R22222 T3 [((0),(163/32)),((0),(405/128)),((0),(405/64)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T4_ok T3145_ok
def T2 : Node := Node.split 1 T3 T3356
theorem T2_ok : Node.check D_R22222 T2 [((0),(163/32)),((0),(405/64)),((0),(405/64)),((0),(163/32))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3_ok T3356_ok
def T1 : Node := Node.split 3 T2 T3597
theorem T1_ok : Node.check D_R22222 T1 [((0),(163/32)),((0),(405/64)),((0),(405/64)),((0),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2_ok T3597_ok
def T0 : Node := Node.split 0 T1 T3762
theorem T0_ok : Node.check D_R22222 T0 [((0),(163/16)),((0),(405/64)),((0),(405/64)),((0),(163/16))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1_ok T3762_ok

end R22222
end ZetaS.CertV2
