section\<open>Defining the properties of type consistency for the basic datatypes Isabelle Hol\<close>
theory TypeSafe_Base_Types
  imports TypeSafe_Hashing_Subs
begin

subsection \<open>Ensuring that String @{type \<open>Valuetype\<close>} conform to their associated datatype @{type \<open>Types\<close>}\<close>
primrec typeCon :: "Types \<Rightarrow> Valuetype \<Rightarrow> bool"      
  where "typeCon (TSInt x) v = checkSInt x v"
  | "typeCon (TUInt x) v = checkUInt x v"
  | "typeCon (TBool) v = checkBool v"
  | "typeCon (TAddr) v = checkAddress v"


lemma typeConNoDots:
  assumes "typeCon t v"
  shows "CHR ''.'' \<notin> set(String.explode v)"
proof(cases t)
  case (TSInt x1)
  then show ?thesis using assms typeCon.simps(1) ShowLIntDot unfolding checkSInt_def by metis
next
  case (TUInt x2)
  then show ?thesis  using assms typeCon.simps(2) ShowLIntDot unfolding checkUInt_def by metis
next
  case TBool
  have "CHR ''.'' \<notin> set (literal.explode STR ''True'')" by eval
  moreover have "CHR ''.'' \<notin> set (literal.explode STR ''False'')" by eval
  ultimately show ?thesis using assms typeCon.simps(3) unfolding checkBool_def 
    using TBool by auto
next
  case TAddr
  then show ?thesis using assms typeCon.simps(4) checkAddress_def by auto
qed

lemma typeCon_no_sublocation_prefix:
  assumes "typeCon x1 i"
  assumes "hash destl  i \<noteq> hash destl x"
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
    moreover have "CHR ''.'' \<notin> set(String.explode i)"  
    proof(cases x1)
      case (TSInt x1)
      then show ?thesis  using typeCon.simps(1)[of x1 i] assms unfolding checkSInt_def using ShowLIntDot by metis
    next
      case (TUInt x2)
      then show ?thesis using typeCon.simps(2)[of x2 i] assms unfolding checkUInt_def using ShowLIntDot by metis
    next
      case TBool
      then have a10:"i = STR ''True'' \<or> i = STR ''False''" using typeCon.simps(3)[of i] assms unfolding checkBool_def  by simp
      have "CHR ''.'' \<notin> set (literal.explode STR ''True'') \<and> CHR ''.'' \<notin> set (literal.explode STR ''False'')" by eval
      then show ?thesis using a10 by auto
    next
      case TAddr
      then show ?thesis using typeCon.simps(4)[of i] assms unfolding checkAddress_def by simp
    qed
    ultimately show False using hash_def 
      using hash_explode by auto
  next 
    assume "hash destl i = hash destl x"
    then show False using assms by simp
  qed
qed

lemma transfer_subRead:
  assumes "transfer ads addr val acc = Some acc'"
    and "addr \<noteq> ads"
    and "typeCon (TUInt b256) val"
    and "typeCon (TUInt b256) (bal (acc ads))"
  shows "(bal (acc' ads)) = ShowL\<^sub>i\<^sub>n\<^sub>t(ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val)"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)

  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' ads)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val" using subBalance_sub[OF *] by simp
  then have "(bal (acc'' ads)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val)" using * unfolding subBalance_def 
    using "*" subBalance_val1 subBalance_val2 by auto
  moreover from assms(2) have "(bal (acc' ads)) = (bal (acc'' ads))" using addBalance_eq[OF **] by simp
  ultimately show ?thesis using Read_ShowL_id  assms by simp
qed

lemma transfer_addRead:
  assumes "transfer ads addr val acc = Some acc'"
    and "addr \<noteq> ads"
    and "typeCon (TUInt b256) val"
    and "typeCon (TUInt b256) (bal (acc addr))"
  shows "(bal (acc' addr)) = ShowL\<^sub>i\<^sub>n\<^sub>t(ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val)"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)
  have ***:"(bal (acc'' addr)) = (bal (acc addr))" 
    using "*" assms(2) subBalance_eq by presburger
  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' addr)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val" using addBalance_add[OF **] by simp
  then have "(bal (acc' addr)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val)" using * ** *** unfolding addBalance_def 
    by (smt (verit, del_insts) account.select_convs(1) account.surjective account.update_convs(1) fun_upd_same option.distinct(1) option.inject)
  then show ?thesis by simp
qed

lemma transfer_sameRead:
  assumes "transfer ads addr val acc = Some acc'"
    and "addr = ads"
    and "typeCon (TUInt b256) val"
    and "typeCon (TUInt b256) (bal (acc ads))"
  shows "(bal (acc' ads)) = (bal (acc ads))"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)
  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ads)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ads))" using transfer_same[OF assms(1) ] assms(2) by simp
  moreover have "(bal (acc'' ads)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val)" using * subBalance_def
    by (smt (verit) account.select_convs(1) account.surjective account.update_convs(1) fun_upd_same option.inject subBalance_val1
        subBalance_val2)
  moreover from ** have ***:"ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ads)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' ads)) + ReadL\<^sub>i\<^sub>n\<^sub>t val" using addBalance_add assms(2) by simp
  moreover have "(bal (acc' addr)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val)" using * ** *** assms(2) unfolding addBalance_def 
    by (smt (verit, best) account.iffs account.surjective account.update_convs(1) fun_upd_same option.distinct(1) option.inject)
  ultimately show ?thesis using Read_ShowL_id  assms 
    by (simp add: checkUInt_def)
qed


end