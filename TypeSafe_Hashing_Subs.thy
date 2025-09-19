section\<open>Defining the properties of generic (store agnostic) sublocations in Isabelle Hol\<close>
theory TypeSafe_Hashing_Subs
  imports Solidity_Main  "HOL-Library.Sublist" 
begin

subsection\<open>Hashing lemmas\<close>
fun location_depth :: "Location \<Rightarrow> nat" where
  "location_depth  s = length (filter (\<lambda>x. x = CHR ''.'') (String.explode s))"

lemma explode_STR_dot: "String.explode (STR ''.'') = [CHR ''.'']"
  using explode_dot by auto

lemma filter_single_dot: "List.filter (\<lambda>x. x = CHR ''.'') [CHR ''.''] = [CHR ''.'']"
  by simp

lemma length_filter_single_dot: "length (List.filter (\<lambda>x. x = CHR ''.'') [CHR ''.'']) = 1"
  by (simp add: filter_single_dot)

lemma location_depth_hash_property:
  "location_depth (hash ls suf) = location_depth ls + location_depth suf + 1" unfolding location_depth.simps
proof -
  have a1:"String.explode (hash ls suf) = (String.explode suf @ String.explode STR ''.'' @ String.explode ls)"
    using hash_explode[of ls suf] by blast
  have "length (filter (\<lambda>x. x = CHR ''.'') (String.explode suf @ String.explode STR ''.'' @ String.explode ls)) =
    length (filter (\<lambda>x. x = CHR ''.'') (literal.explode ls)) + length (filter (\<lambda>x. x = CHR ''.'') (literal.explode suf)) + 1 "
    by simp
  show "length (filter (\<lambda>x. x = CHR ''.'') (literal.explode (hash ls suf))) =
    length (filter (\<lambda>x. x = CHR ''.'') (literal.explode ls)) + length (filter (\<lambda>x. x = CHR ''.'') (literal.explode suf)) + 1 "
    using a1 by simp 
qed

lemma hash_adds_depth: 
  assumes "CHR ''.'' \<notin> set (String.explode suf) "
  shows "location_depth ((hash ls suf)) = location_depth (ls) + 1" 
proof - 
  have "location_depth suf = 0" using assms filter_False length_0_conv 
    by (metis (full_types, lifting) location_depth.simps)
  then show "location_depth (hash ls suf) = location_depth ls + 1 " using location_depth_hash_property by presburger
qed

(*Shows that hashing a string to another string cannot result in the same string*)
lemma hash_inequality: "\<forall>suffix. (hash ls suffix) \<noteq> ls "
proof
  fix suffix
  have " (hash ls suffix) = suffix + (STR ''.'' + ls)"
    unfolding hash_def by simp
  also have "ls =  ls"
    by simp
  ultimately show "hash ls suffix  \<noteq>  ls"
    using Literal.rep_eq plus_literal.rep_eq literal.explode_inject unfolding hash_def nat_explode_def ShowL\<^sub>n\<^sub>a\<^sub>t_def String.implode_def Show\<^sub>n\<^sub>a\<^sub>t_def 
    by (metis (no_types, lifting) add.assoc self_append_conv2 snoc_eq_iff_butlast zero_literal.rep_eq)
qed

lemma hash_version_inequality: "\<forall>suffix. (hash_version ls suffix) \<noteq> ls "
proof
  fix suffix
  have " (hash_version ls suffix) = suffix + (STR ''-'' + ls)"
    unfolding hash_version_def by blast
  also have "ls =  ls"
    by simp
  ultimately show "hash_version ls suffix  \<noteq>  ls"
    using Literal.rep_eq plus_literal.rep_eq literal.explode_inject 
    unfolding hash_def nat_explode_def ShowL\<^sub>n\<^sub>a\<^sub>t_def String.implode_def Show\<^sub>n\<^sub>a\<^sub>t_def 
    by (metis (no_types, lifting) add.assoc self_append_conv2 snoc_eq_iff_butlast zero_literal.rep_eq)
qed

value "hash (STR ''1'') (STR ''2'')"
value "hash (STR ''2.1'') (STR ''3'')"
value "hash (STR ''2'') (STR ''3'')"
value "hash (STR ''1'') (STR ''3.2'')"
value "hash (STR ''2'') (STR ''1.0'')"
value "hash (STR ''2'') (hash (STR ''0'') (STR ''1''))"

lemma hash_suffixes_associative: "(hash (hash ls suffix1) suffix2) = (hash ls (hash suffix1 suffix2))"
  unfolding hash_def by (simp add: add.assoc)

lemma not_equal_string:
  assumes "s1\<noteq>s2"
  shows "String.explode s1 \<noteq> String.explode s2" 
  by (simp add: assms literal.explode_inject)

(*If the prefix to an address is not equal then the result of hashing is never equal*)
lemma hash_never_equal_prefix:
  assumes "s1 \<noteq> s2"
  shows "\<forall>iter1. (hash s1 iter1) \<noteq> hash s2 iter1"
proof intros
  fix iter1 
  show "(hash s1 iter1) \<noteq> hash s2 iter1"
  proof(rule ccontr)
    assume *:"\<not> hash s1 iter1 \<noteq> hash s2 iter1"
    then have **:"hash s1 iter1 = hash s2 iter1" by simp
    then have a10:"String.explode (hash s1 iter1) = String.explode (hash s2 iter1)" by simp
    have a15:"String.explode (hash s1 iter1) = literal.explode iter1 @ literal.explode STR ''.'' @ literal.explode s1"  using hash_explode by simp
    have a20:"String.explode (hash s2 iter1) = literal.explode iter1 @ literal.explode STR ''.'' @ literal.explode s2"  using hash_explode by simp
    then have "literal.explode s1 = literal.explode s2" using a10 a15 a20 same_append_eq[of "literal.explode iter1 @ literal.explode STR ''.''" "literal.explode s1" "literal.explode s2"] by simp
    then show False using assms not_equal_string by simp
  qed
qed

(*If the base address (sufix) is not equal then the hased address can never be equal*)
lemma hash_never_equal_sufix:
  assumes "s1 \<noteq> s2"
  shows "\<forall>iter1. (hash iter1 s1) \<noteq> hash iter1 s2"
proof intros
  fix iter1 
  show "hash iter1 s1 \<noteq> hash iter1 s2"
  proof(rule ccontr)
    assume *:"\<not> hash iter1 s1 \<noteq> hash iter1 s2"
    then have **:"hash iter1 s1 = hash iter1 s2" by simp
    then have a10:"String.explode (hash iter1 s1) = String.explode (hash iter1 s2)" by simp
    have a15:"String.explode (hash iter1 s1) = literal.explode s1 @ literal.explode STR ''.'' @ literal.explode iter1"  using hash_explode by simp
    have a20:"String.explode (hash iter1 s2) = literal.explode s2 @ literal.explode STR ''.'' @ literal.explode iter1"  using hash_explode by simp
    then have "literal.explode s1 = literal.explode s2" using a10 a15 a20 same_append_eq by simp
    then show False using assms not_equal_string by simp
  qed
qed

lemma hash_never_equal_sufix_dots:
  assumes "s1 \<noteq> s2"
    and "CHR ''.'' \<notin> set(String.explode s1)" 
    and "CHR ''.'' \<notin> set(String.explode s2)"
  shows "\<forall>iter1 iter2. hash iter1 s1 \<noteq> hash iter2 s2"
proof intros
  fix iter1 iter2
  show "hash iter1 s1 \<noteq> hash iter2 s2"
  proof(rule ccontr)
    assume *:"\<not> hash iter1 s1 \<noteq> hash iter2 s2"
    then have **:"hash iter1 s1 = hash iter2 s2" by simp
    then have a10:"String.explode (hash iter1 s1) = String.explode (hash iter2 s2)" by simp
    have a15:"String.explode (hash iter1 s1) = literal.explode s1 @ literal.explode STR ''.'' @ literal.explode iter1"  using hash_explode by simp
    have a20:"String.explode (hash iter2 s2) = literal.explode s2 @ literal.explode STR ''.'' @ literal.explode iter2"  using hash_explode by simp
    then have "literal.explode s1 = literal.explode s2" using a10 a15 a20 assms  
      by (metis "**" hash_injective)
    then show False using assms not_equal_string by simp
  qed
qed

lemma hashes_same:
  assumes "hash ad x = y"
    and "hash ad' x = y"
  shows "ad' = ad" using assms 
  using hash_never_equal_prefix by auto 

definition LSubPrefL2::"Location \<Rightarrow> Location \<Rightarrow> bool" 
  where "LSubPrefL2 moreSpecificThanParent parent = 
      ((\<exists>i. moreSpecificThanParent = (hash parent i)) \<or> moreSpecificThanParent = parent)"

lemma subPrefCannotBeInt:
  assumes "CHR ''.'' \<notin> set(String.explode l)"
  shows "\<not>(\<exists>i. l = i + (STR ''.'' + stl2))"
proof (rule ccontr)
  assume "\<not> (\<nexists>i. l = i + (STR ''.'' + stl2))"
  then have a10: "(\<exists>i. l = i + (STR ''.'' + stl2))" by auto
  then show False using assms 
    using plus_literal.rep_eq by fastforce
qed

lemma hash_int_prefix:
  assumes "hash destl  i \<noteq> hash destl x"
    and "CHR ''.'' \<notin> set(String.explode i)"
    and "CHR ''.'' \<notin> set(String.explode x)"
  shows "\<not> LSubPrefL2 (hash destl i) (hash destl x)"
  unfolding LSubPrefL2_def
proof 
  assume "(\<exists>ia. hash destl i = hash (hash destl x) ia) \<or> hash destl i = hash destl x"
  then show False
  proof
    assume "\<exists>ia. hash destl i = hash (hash destl x) ia"
    then have "\<exists>ia. hash destl i = hash destl (hash x ia)" 
      by (simp add: hash_suffixes_associative)
    then have "\<exists>ia. i = (hash x ia)"
      using hash_never_equal_sufix by auto
    then obtain ia where "i = (hash x ia)" by auto
    moreover have "CHR ''.'' \<notin> set(String.explode i)"  using assms by simp
    ultimately show False using hash_def 
      using hash_explode by auto
  next 
    assume "hash destl i = hash destl x"
    then show False using assms by simp

  qed

qed


lemma Not_Sub_More_Specific:
  assumes "\<not> LSubPrefL2 destl' destl"
  shows "\<not> LSubPrefL2 destl' (hash destl x)" 
proof  
  assume a10:"LSubPrefL2 destl' (hash destl x)"
  have "\<not>((\<exists>i. destl' = hash destl  i) \<or> destl' =  destl)" using assms LSubPrefL2_def by simp
  then have *:"(\<forall>i. destl' \<noteq> hash destl  i)" and **:"destl' \<noteq>  destl" by simp+
  have "((\<exists>i. destl' = hash (hash destl x) i) \<or> destl' = hash destl x)" using LSubPrefL2_def[of destl' "(hash destl x)"] a10 by simp
  then show False 
  proof 
    assume "\<exists>i. destl' = hash (hash destl x) i"
    then have "\<exists>i. destl' = hash destl (hash  x i)" unfolding hash_def by (simp add: add.assoc)
    then show False using * by simp
  next 
    assume "destl' = hash destl x "
    then show False using * by simp
  qed
qed


lemma suffix_eq_hard:
	assumes "b @ a = d @ c"
	  and	"b \<noteq> d"
	shows	"strict_prefix b d \<or> strict_prefix d b"
	apply auto
	using assms
	by (metis prefixI prefix_order.less_le prefix_same_cases)

lemma suffix_eq_harder:
	assumes "b @ s @ a = d @ s @ c"
	  and	"b \<noteq> d"
	shows	"strict_prefix b d \<or> strict_prefix d b"
	apply auto
	using assms
	by (metis prefixI prefix_order.less_le prefix_same_cases)

lemma Mutual_NonSub_SpecificNonSub:
  assumes "\<not>LSubPrefL2 destl'  destl \<and> \<not>LSubPrefL2 destl  destl'"
  shows "\<not>LSubPrefL2 (hash destl' x) destl"
proof
  assume a10:"LSubPrefL2 (hash destl' x) destl"
  have "\<not>((\<exists>i. destl' = hash destl  i) \<or> destl' =  destl)" using assms LSubPrefL2_def by simp
  then have b10:"(\<forall>i. destl' \<noteq> hash destl  i)" and b20:"destl' \<noteq>  destl" by simp+
  have "\<not>((\<exists>i. destl = hash destl'  i) \<or> destl' =  destl)" using assms LSubPrefL2_def by simp
  then have b30:"(\<forall>i. destl \<noteq> hash destl'  i)" and b40:"destl' \<noteq>  destl" by simp+
  have "((\<exists>i. hash destl' x = hash destl i) \<or> hash destl' x = destl)" using LSubPrefL2_def[of "(hash destl' x) " "destl"] a10 by simp
  then show False
  proof 
    assume "\<exists>i. hash destl' x = hash destl i"
    then show False 
    proof 
      fix xa
      assume b50:" hash destl' x = hash destl xa"
      then show False
      proof(cases "x=xa")
        case True
        then show ?thesis using b50 b40 hash_never_equal_prefix by auto
      next
        case False
        then have a10:"String.explode (hash destl' x) = String.explode (hash destl xa)" using b50 by simp
        have a15:"String.explode (hash destl' x) = literal.explode x @ literal.explode STR ''.'' @ literal.explode destl'"  using hash_explode by simp
        have a20:"String.explode (hash destl xa) = literal.explode xa @ literal.explode STR ''.'' @ literal.explode destl"  using hash_explode by simp
        then have "strict_prefix (literal.explode x) (literal.explode xa) \<or> strict_prefix (literal.explode xa) (literal.explode x)"
          using suffix_eq_harder[of "literal.explode x" "literal.explode STR ''.''" "literal.explode destl'" " literal.explode xa" "literal.explode destl"] 
          using a10 a15 a20 False by (simp add: not_equal_string)
        then show ?thesis
        proof
          assume a30:"strict_prefix (literal.explode x) (literal.explode xa)"
          then obtain zs where zs:"literal.explode xa = literal.explode x @ zs" using strict_prefix_def prefix_def[of " (literal.explode x)" " (literal.explode xa)"]
            by auto
          then have a40:"zs @ literal.explode STR ''.'' @ literal.explode destl = literal.explode STR ''.'' @ literal.explode destl'" using a10 a20 a15 by simp
          then obtain pl where pl2:"literal.explode STR ''.'' @ pl = zs"  by (metis Literal.rep_eq a30 append.right_neutral append_Cons append_self_conv2 list.exhaust prefix_order.less_imp_not_less strict_prefixI' strict_prefix_simps(3) zero_literal.rep_eq zs)
          then have a70:"pl @ literal.explode STR ''.'' @ literal.explode destl =  literal.explode destl'" using a40 by auto
          have "map String.ascii_of pl = pl" using pl2 zs a30 by (metis String.implode_explode_eq implode.rep_eq map_append same_append_eq) 
          then have a90:"(pl @ literal.explode STR ''.'' @ literal.explode destl) = literal.explode (hash destl (String.implode pl))" using  hash_explode[of destl "(String.implode pl)"] by simp
          have a80:"(\<forall>i. literal.explode destl' \<noteq> literal.explode (hash destl  i))" using b10 by (simp add: not_equal_string)
          then have "\<forall>i. literal.explode destl' \<noteq> literal.explode i @ literal.explode STR ''.'' @ literal.explode destl" by (simp add: hash_explode)
          then show False using a70 a80 a90 by presburger
        next 
          assume a30:"strict_prefix (literal.explode xa) (literal.explode x)"
          then obtain zs where zs:"literal.explode x = literal.explode xa @ zs" using strict_prefix_def prefix_def[of " (literal.explode xa)" " (literal.explode x)"]
            by auto
          then have a40:"literal.explode STR ''.'' @ literal.explode destl = zs @ literal.explode STR ''.'' @ literal.explode destl'" using a10 a20 a15 by simp
          then obtain pl where pl2:"literal.explode STR ''.'' @ pl = zs"  by (metis Literal.rep_eq a30 append.right_neutral append_Cons append_self_conv2 list.exhaust prefix_order.less_imp_not_less strict_prefixI' strict_prefix_simps(3) zero_literal.rep_eq zs)
          then have a70:"pl @ literal.explode STR ''.'' @ literal.explode destl' =  literal.explode destl" using a40 by auto
          have "map String.ascii_of pl = pl" using pl2 zs a30 by (metis String.implode_explode_eq implode.rep_eq map_append same_append_eq) 
          then have a90:"(pl @ literal.explode STR ''.'' @ literal.explode destl') = literal.explode (hash destl' (String.implode pl))" using  hash_explode[of destl' "(String.implode pl)"] by simp
          have a80:"(\<forall>i. literal.explode destl \<noteq> literal.explode (hash destl'  i))" using b30 by (simp add: not_equal_string)
          then have "\<forall>i. literal.explode destl \<noteq> literal.explode i @ literal.explode STR ''.'' @ literal.explode destl'" by (simp add: hash_explode)
          then show False using a70 a80 a90 by presburger
        qed
      qed
    qed
  next 
    assume " hash destl' x = destl"
    then show False using b30 by auto
  qed
qed

lemma hashesIntSame:
  assumes "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) = y"
    and "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i') = y"
  shows "i = i'" using assms
  by (metis Read_Show_nat'_id hash_never_equal_sufix)

lemma hashesInts:
  assumes "hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) z = y"
    and "hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i')) z' = y"
  shows "i = i'" using assms ShowLNatDot
  by (metis LSubPrefL2_def Read_Show_nat'_id Mutual_NonSub_SpecificNonSub hash_int_prefix hash_never_equal_sufix)

lemma hashesAssociative:
  assumes "hash (hash destl  i) z = y"
    and "hash (hash destl i') z' = y"
    and "CHR ''.'' \<notin> set(String.explode i)"
    and "CHR ''.'' \<notin> set(String.explode i')"

shows "i = i'" using assms ShowLNatDot
  by (metis LSubPrefL2_def Mutual_NonSub_SpecificNonSub hash_int_prefix hash_never_equal_sufix)

lemma readLintNotEqual:
  assumes "(ReadL\<^sub>n\<^sub>a\<^sub>t suffix')<(ReadL\<^sub>n\<^sub>a\<^sub>t suffixa)"
  shows "suffix' \<noteq> suffixa" using assms unfolding ReadL\<^sub>n\<^sub>a\<^sub>t_def Read\<^sub>n\<^sub>a\<^sub>t_def nat_implode_def nat_of_digit_def by blast



lemma checkUIntIncreaseB:
  assumes "(ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^b)"
    and "b\<le>b2"
  shows "(ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^b2)"
proof
  show "0 \<le>ReadL\<^sub>i\<^sub>n\<^sub>t v" using assms by simp
next
  show "ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^b2" using assms
    by (metis take_bit_int_eq_self_iff take_bit_int_greater_eq_self_iff take_bit_tightened_less_eq_int)
qed

lemma ShowLnat_ReadLint_inverse:
  assumes "0 \<le> ReadL\<^sub>i\<^sub>n\<^sub>t(kv)"
    and "ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t kv) = kv"
  shows "(ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))) = kv"
proof(cases "(ReadL\<^sub>i\<^sub>n\<^sub>t kv)")
  case (nonneg n)
  then have a10:"(ReadL\<^sub>i\<^sub>n\<^sub>t kv) = Read\<^sub>i\<^sub>n\<^sub>t ( String.explode kv)" using ReadL\<^sub>i\<^sub>n\<^sub>t_def by (metis comp_apply)
  then have a20:"(ReadL\<^sub>i\<^sub>n\<^sub>t kv) = int n" using nonneg by simp
  then have a30: "int n = Read\<^sub>i\<^sub>n\<^sub>t ( String.explode kv)" using a10 a20 by simp
  then have a40:"int n = int (Read\<^sub>n\<^sub>a\<^sub>t (String.explode kv))" 
  proof(cases "hd (literal.explode kv) = CHR ''-''")
    case headkv:True
    then have a50:"int n = - int (Read\<^sub>n\<^sub>a\<^sub>t (tl (literal.explode kv)))" using a30 Read\<^sub>i\<^sub>n\<^sub>t_def by simp
    then have a60:"int n \<le> 0" by simp
    show ?thesis
    proof(cases "n = 0")
      case True
      then have a80:"- int (Read\<^sub>n\<^sub>a\<^sub>t (tl (literal.explode kv))) = 0" using a50 by simp
      have "ShowL\<^sub>i\<^sub>n\<^sub>t 0 =  String.implode (Show\<^sub>i\<^sub>n\<^sub>t 0)" using ShowL\<^sub>i\<^sub>n\<^sub>t_def by (metis comp_apply)
      then have a100:"ShowL\<^sub>i\<^sub>n\<^sub>t 0 = String.implode ( Show\<^sub>n\<^sub>a\<^sub>t (nat 0))" using Show\<^sub>i\<^sub>n\<^sub>t_def by simp
      then have "hd(Show\<^sub>n\<^sub>a\<^sub>t (nat 0)) \<noteq>  CHR ''-''" using Show\<^sub>n\<^sub>a\<^sub>t_def Show_nat_not_neg'' by simp
      then have a120:"hd (literal.explode kv) \<noteq> hd(Show\<^sub>n\<^sub>a\<^sub>t (nat 0))" using headkv by auto
      then show ?thesis using assms(2) a30 a20 nonneg headkv a50 a80 a100 a120 String.implode_def using Show\<^sub>n\<^sub>a\<^sub>t_ascii by fastforce
    next
      case False
      then have "n<0" using a60 by simp
      then show ?thesis using nonneg by simp
    qed
  next
    case False
    then show ?thesis using a30 Read\<^sub>i\<^sub>n\<^sub>t_def by simp
  qed
  have "nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv) = nat(int (Read\<^sub>n\<^sub>a\<^sub>t (String.explode kv)))" using a40 a30 by (simp add: nonneg)
  then show ?thesis using assms(2) assms(1) comp_apply unfolding ShowL\<^sub>i\<^sub>n\<^sub>t_def Show\<^sub>i\<^sub>n\<^sub>t_def ShowL\<^sub>n\<^sub>a\<^sub>t_def by simp
next
  case (neg n)
  then show ?thesis using assms by simp
qed

lemma notNoneUpdate:
  assumes "st' = st\<lparr>stack := updateStore l v (stack st), gas:=g\<rparr>"
  shows "accessStore l (stack st') = Some v" using assms by fastforce

lemma MemLSubPrefL2_specific_imps_general:
  assumes "LSubPrefL2 (hash p y) (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
  shows "LSubPrefL2  p (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" 
proof -
  have a10:"((\<exists>i. hash p y = hash (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) i) \<or> hash p y = (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))" using assms LSubPrefL2_def[of "hash p y" "(ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"] by blast
  have a20:" hash p y \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ShowLNatDot hash_def 
    by (metis subPrefCannotBeInt)
  then have a30:"(\<exists>i. hash p y = hash (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) i)" using a10 by auto
  then obtain i where idef:"hash p y = hash (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) i" by blast
  then show ?thesis
  proof(cases "i = y")
    case True
    then have "p = (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using a30 
      using idef hash_never_equal_prefix by auto
    then show ?thesis 
      by (simp add: LSubPrefL2_def)
  next
    case False
    then have a40:"p \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using idef 
      using hash_never_equal_sufix by auto
    then have "\<exists>h. hash (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) h = p" using idef False ShowLNatDot hash_def 
      by (metis LSubPrefL2_def Mutual_NonSub_SpecificNonSub subPrefCannotBeInt)
    then show ?thesis 
      using LSubPrefL2_def by auto
  qed
qed

subsection \<open>MISC\<close>
lemma checkSIntIncreaseB:
  assumes "(ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> -(2^(b-1)) \<and> ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^(b-1))"
    and "b\<le>b2"
  shows "(ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> -(2^(b2-1)) \<and> ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^(b2-1))"
proof -
  have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> -(2^(b2-1))" using assms dual_order.trans by fastforce
  moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^(b2-1)" using assms 
    by (metis checkUIntIncreaseB diff_le_mono order.asym take_bit_int_greater_self_iff take_bit_int_less_self_iff verit_comp_simplify1(3))
  ultimately show ?thesis by simp
qed

lemma checkUIntToSInt:
  assumes "(ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^b)"
    and "b<b2"
  shows "(ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> -(2^(b2-1)) \<and> ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^(b2-1))"
proof -
  have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> -(2^(b2-1))" using assms dual_order.trans by fastforce
  moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^(b2-1)" using assms 
    by (metis One_nat_def Suc_leI Suc_pred cancel_comm_monoid_add_class.diff_cancel checkUIntIncreaseB less_imp_diff_less verit_comp_simplify1(3))
  ultimately show ?thesis by simp
qed

subsection \<open>Additional Hash Helper Lemmas\<close>


(*Hash length and structure properties*)
lemma hash_length_increase:
  "length (String.explode (hash a b)) = length (String.explode a) + length (String.explode b) + 1"
proof -
  have "String.explode (hash a b) = literal.explode b @ literal.explode STR ''.'' @ literal.explode a"
    using hash_explode by simp
  then show ?thesis by simp
qed

lemma hash_min_length:
  "length (String.explode (hash a b)) \<ge> 1"
proof -
  have "length (String.explode (hash a b)) = length (String.explode a) + length (String.explode b) + 1"
    using hash_length_increase by simp
  then show ?thesis by simp
qed

lemma hash_contains_dot:
  "CHR ''.'' \<in> set (String.explode (hash a b))"
proof -
  have "String.explode (hash a b) = literal.explode b @ literal.explode STR ''.'' @ literal.explode a"
    using hash_explode by simp
  then show ?thesis using explode_STR_dot by auto
qed

(*Hash component extraction lemmas*)
lemma hash_prefix_extraction:
  assumes "s = hash a b"
  shows "\<exists>pre suf. String.explode s = pre @ [CHR ''.''] @ suf \<and> 
                    String.implode pre = b \<and> String.implode suf = a"
proof -
  have "String.explode s = literal.explode b @ literal.explode STR ''.'' @ literal.explode a"
    using assms hash_explode by simp
  then have "String.explode s = literal.explode b @ [CHR ''.''] @ literal.explode a"
    using explode_STR_dot by simp
  then show ?thesis by (metis String.implode_explode_eq)
qed

lemma hash_suffix_from_prefix:
  assumes "hash a b = hash c d"
    and "a = c"
  shows "b = d"
  using assms hash_never_equal_sufix by auto

lemma hash_flatten_right:
  "hash a (hash b c) = hash (hash a b) c"
  using hash_suffixes_associative by simp

lemma hash_depth_nested:
  assumes "CHR ''.'' \<notin> set (String.explode a)"
    and "CHR ''.'' \<notin> set (String.explode b)"
  shows "location_depth (hash (hash base a) b) = location_depth base + 2"
proof -
  have "location_depth (hash base a) = location_depth base + 1"
    using assms(1) hash_adds_depth by simp
  then have "location_depth (hash (hash base a) b) = location_depth (hash base a) + 1"
    using assms(2) hash_adds_depth by simp
  then show ?thesis using \<open>location_depth (hash base a) = location_depth base + 1\<close> by simp
qed

(*Hash ordering and normalization properties*)
lemma hash_canonical_form:
  "hash a b = b + STR ''.'' + a"
  unfolding hash_def 
  by (simp add: add.assoc)

lemma hash_nested_equality_implies_index_equality:
  assumes "x3 = hash ld (hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) (ShowL\<^sub>n\<^sub>a\<^sub>t ia))"
    and "(\<exists>ia'. hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = hash (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ia') \<or> hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
  shows "i = x"
proof (cases "(\<exists>ia'. hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = hash (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ia')")
  case True
  then obtain ia' where ia'_def: "hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = hash (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ia'" by blast
  have "hash (hash ld (hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) (ShowL\<^sub>n\<^sub>a\<^sub>t ia))) (ShowL\<^sub>n\<^sub>a\<^sub>t i) = hash (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ia'" 
    using assms(1) ia'_def hash_suffixes_associative by simp
  then have "hash ld (hash (hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) (ShowL\<^sub>n\<^sub>a\<^sub>t ia)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = hash ld (hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) ia')"
    by (simp add: hash_suffixes_associative)
  then have "hash (hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) (ShowL\<^sub>n\<^sub>a\<^sub>t ia)) (ShowL\<^sub>n\<^sub>a\<^sub>t i) = hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) ia'"
    using hash_injective ShowLNatDot 
    by (meson hash_never_equal_sufix)
  then have "hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) (hash (ShowL\<^sub>n\<^sub>a\<^sub>t ia) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) ia'"
    by (simp add: hash_suffixes_associative)
  then have "ShowL\<^sub>n\<^sub>a\<^sub>t i = ShowL\<^sub>n\<^sub>a\<^sub>t x"
    using hash_injective ShowLNatDot 
    by (metis hash_flatten_right hashesInts)
  then show "i = x" by (metis Read_Show_nat'_id)
next
  case False
  then have "hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using assms(2) by blast
  have "hash (hash ld (hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) (ShowL\<^sub>n\<^sub>a\<^sub>t ia))) (ShowL\<^sub>n\<^sub>a\<^sub>t i) = hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
    using assms(1) \<open>hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> hash_suffixes_associative by simp
  then have "hash ld (hash (hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) (ShowL\<^sub>n\<^sub>a\<^sub>t ia)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
    by (simp add: hash_suffixes_associative)
  then have "hash (hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) (ShowL\<^sub>n\<^sub>a\<^sub>t ia)) (ShowL\<^sub>n\<^sub>a\<^sub>t i) = ShowL\<^sub>n\<^sub>a\<^sub>t x"
    using hash_injective ShowLNatDot by (meson hash_never_equal_sufix)
  then have "hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) (hash (ShowL\<^sub>n\<^sub>a\<^sub>t ia) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = ShowL\<^sub>n\<^sub>a\<^sub>t x"
    by (simp add: hash_suffixes_associative)
  then have "ShowL\<^sub>n\<^sub>a\<^sub>t i = ShowL\<^sub>n\<^sub>a\<^sub>t x"
    using hash_injective ShowLNatDot 
    by (metis hash_contains_dot)
  then show "i = x" by (metis Read_Show_nat'_id)
qed

lemma MemLSubPrefTransitive:
  assumes "LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
    and "LSubPrefL2 loc p'"
  shows "LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" 
proof - 
  have a5:"\<not>(\<exists>x. hash p' x = (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))" using hash_def ShowLNatDot 
    by (metis append_Cons explode_dot hash_explode in_set_conv_decomp)
  obtain pre1 where a10: "hash (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) pre1 = loc \<or> loc = (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using assms(1) 
    using LSubPrefL2_def by auto
  obtain pre2 where a20:"hash p' pre2 = loc \<or> loc = p'" using assms(2) 
    using LSubPrefL2_def by auto
  have "((\<exists>i. p' = hash (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) i) \<or> p' = (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))" 
  proof(cases "pre1 = pre2")
    case t1:True
    then show ?thesis 
    proof(cases "loc = (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)")
      case t2:True
      then show ?thesis 
        using a20 a5 by auto
    next
      case False
      then show ?thesis 
        using a10 a20 hash_never_equal_prefix t1 by auto
    qed
  next
    case False
    then show ?thesis 
      by (metis LSubPrefL2_def a20 a5 assms(1) Mutual_NonSub_SpecificNonSub)
  qed
  then show ?thesis  using LSubPrefL2_def[of p' "(ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"] by simp
qed

end 