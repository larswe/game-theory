theory Game_Theory 
  imports "HOL-Analysis.Analysis"
begin

section "Defining a Simultaneous Move Game"

locale strategic_game = 
  fixes possible_strategies :: "'player :: finite  \<Rightarrow> 'strategy set"
    and payoffs :: "'strategy^'player \<Rightarrow> ('payoff :: linorder)^'player"
assumes players_can_play: "possible_strategies i \<noteq> {}"
begin

corollary players_have_a_move: "\<exists>s. s\<in>possible_strategies i"
  using players_can_play by auto 

text "Strategy selection"
(* TODO - Change the names to pure_profile etc. . *)
definition strategy_maps :: "('player \<Rightarrow> 'strategy) set"
  where "strategy_maps = {f. \<forall>i. f i \<in> possible_strategies i}"

definition strategy_vector :: "('player \<Rightarrow> 'strategy) \<Rightarrow> 'strategy^'player" 
  where "strategy_vector f = (\<chi> i. f i)"

definition strategy_vectors :: "('strategy^'player) set"
  where "strategy_vectors = {s. \<exists>f. (s = strategy_vector f \<and> f \<in> strategy_maps)}"

definition payoff :: "'strategy^'player \<Rightarrow> 'player \<Rightarrow> 'payoff" 
  where "payoff s i = (payoffs s)$i"

lemma strategy_vector_iff:
  fixes s :: "'strategy^'player"
  shows "(s \<in> strategy_vectors) = (\<forall>i. s$i \<in> possible_strategies i)"
  by (smt (verit, del_insts) mem_Collect_eq strategy_maps_def strategy_vector_def 
     strategy_vectors_def vec_lambda_beta vec_lambda_eta) (* TODO - Make nice *)

lemma strategy_map_fix_exists: 
  fixes s\<^sub>i :: "'strategy" 
  assumes fixed_strategy:  "s\<^sub>i \<in> possible_strategies i" 
  shows "\<exists>f. f \<in> strategy_maps \<and> f i = s\<^sub>i"
proof -
  let ?s' = "(\<lambda>j. (if j = i then s\<^sub>i else (SOME s. s \<in> possible_strategies j)))" 
  have "\<forall>i. ?s' i \<in> (possible_strategies i)"
    by (simp add: players_can_play some_in_eq fixed_strategy) 
  hence "?s' \<in> strategy_maps"
    using strategy_maps_def by simp 
  thus ?thesis 
    by auto 
qed

lemma strategy_map_exists: "\<exists>f. f \<in> strategy_maps"
  using strategy_map_fix_exists players_have_a_move by blast 

lemma strategy_vector_fix_exists: 
  fixes s\<^sub>i :: "'strategy" 
  assumes fixed_strategy:  "s\<^sub>i \<in> possible_strategies i" 
  shows "\<exists>s. s \<in> strategy_vectors \<and> s$i = s\<^sub>i" 
proof - 
  obtain f where "f \<in> strategy_maps \<and> f i = s\<^sub>i"
    using fixed_strategy strategy_map_fix_exists by auto 
  hence "(strategy_vector f) \<in> strategy_vectors \<and> (strategy_vector f)$i = s\<^sub>i"
    by (simp add: strategy_vector_def strategy_vectors_def)
  thus ?thesis 
    by auto 
qed

lemma strategy_vector_exists: "\<exists>s. s \<in> strategy_vectors" 
  using strategy_vector_fix_exists players_have_a_move by blast 

lemma unilateral_mode_exists: "\<exists>f. \<forall>i. \<forall>s\<^sub>i \<in> (possible_strategies i). 
         (f i s\<^sub>i) \<in> strategy_vectors \<and> (f i s\<^sub>i)$i = s\<^sub>i \<and> 
         (\<forall>j. ((j \<noteq> i) \<longrightarrow> (\<forall>s'\<in>(possible_strategies i). (f i s')$j = (f i s\<^sub>i)$j)))"
proof (rule exI)
  let ?h = "(SOME h. h \<in> strategy_maps)"
  let ?g = "(\<lambda>i s\<^sub>i. (\<lambda>j. if j = i then s\<^sub>i else ?h j))"
  let ?f = "(\<lambda>i s\<^sub>i. strategy_vector (?g i s\<^sub>i))"
  have "?h \<in> strategy_maps"
    using some_in_eq strategy_map_exists by auto
  hence "\<forall>i. \<forall>s\<^sub>i \<in> (possible_strategies i). ?g i s\<^sub>i \<in> strategy_maps"
    by (simp add: strategy_maps_def)
  hence "\<forall>i. \<forall>s\<^sub>i \<in> (possible_strategies i). (?f i s\<^sub>i) \<in> strategy_vectors"
    using strategy_vectors_def by auto 
  moreover have "\<forall>i. \<forall>s\<^sub>i \<in> (possible_strategies i). (?f i s\<^sub>i)$i = s\<^sub>i"
    by (simp add: strategy_vector_def)
  moreover have "\<forall>i. \<forall>s\<^sub>i \<in> (possible_strategies i). 
               ((\<forall>j. ((j \<noteq> i) \<longrightarrow> 
                (\<forall>s'\<in>(possible_strategies i). (?f i s')$j = (?f i s\<^sub>i)$j))))"
    using strategy_vector_def by auto 
  ultimately show "\<forall>i. \<forall>s\<^sub>i \<in> (possible_strategies i). 
         (?f i s\<^sub>i) \<in> strategy_vectors \<and> (?f i s\<^sub>i)$i = s\<^sub>i \<and> 
         (\<forall>j. ((j \<noteq> i) \<longrightarrow> (\<forall>s'\<in>(possible_strategies i). (?f i s')$j = (?f i s\<^sub>i)$j)))"
    by blast
qed

(* s_-i = function that maps each of i's actions to the according play *)


definition play_completion :: "'strategy \<Rightarrow> 'strategy^'player \<Rightarrow> 'player \<Rightarrow> 'strategy^'player"
  where "play_completion s\<^sub>i s i = (\<chi> j. if j = i then s\<^sub>i else s$j)"

notation play_completion ("(_,_\<^sub>-\<^sub>_)" [80, 80] 80)

lemma player_chooses_completion: "(s\<^sub>i,s\<^sub>-\<^sub>i)$i = s\<^sub>i"
  by (simp add: play_completion_def)

lemma completion_fixes_other_players: 
  fixes i :: 'player
    and j :: 'player
  assumes "i \<noteq> j"
  shows "(s\<^sub>i,s\<^sub>-\<^sub>i)$j = s$j"
  using assms play_completion_def by auto

lemma completion_legal_iff: 
  fixes i :: 'player 
    and s :: "'strategy^'player"
  shows "((s\<^sub>i,s\<^sub>-\<^sub>i) \<in> strategy_vectors) = ((s\<^sub>i \<in> possible_strategies i) \<and> 
        (\<forall>j. ((j \<noteq> i) \<longrightarrow> s$j \<in> possible_strategies j)))"
proof - 
  have "((s\<^sub>i,s\<^sub>-\<^sub>i) \<in> strategy_vectors) = (\<forall>j. (s\<^sub>i,s\<^sub>-\<^sub>i)$j \<in> possible_strategies j)"
    by (simp add: strategy_vector_iff)
  hence "((s\<^sub>i,s\<^sub>-\<^sub>i) \<in> strategy_vectors) = (((s\<^sub>i,s\<^sub>-\<^sub>i)$i \<in> possible_strategies i) \<and>
         (\<forall>j. ((j \<noteq> i) \<longrightarrow> (s\<^sub>i,s\<^sub>-\<^sub>i)$j \<in> possible_strategies j)))"
    by auto
  thus ?thesis
    by (simp add: player_chooses_completion completion_fixes_other_players)
qed

end

text "Strategic form games with real-valued payoffs."
locale real_out_strategic_game = strategic_game possible_strategies payoffs
  for payoffs :: "('strategy, 'player) vec \<Rightarrow> (real, 'player :: finite) vec"
  and possible_strategies
begin

text "For real-valued payoffs, costs can be defined to be their additive inverse."
definition costs :: "('strategy, 'player) vec \<Rightarrow> (real, 'player) vec"
  where "costs s = -(payoffs s)"

definition cost :: "('strategy, 'player) vec \<Rightarrow> 'player \<Rightarrow> real"
  where "cost s i = (costs s)$i"

lemma cost_neg_pay: 
  shows "cost s i = -(payoff s i)"
  by (simp add: cost_def costs_def payoff_def)

end

end