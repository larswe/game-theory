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
definition strategy_funs :: "('player \<Rightarrow> 'strategy) set"
  where "strategy_funs = {f. \<forall>i. f i \<in> possible_strategies i}"

definition fun_to_vec :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b^'a" 
  where "fun_to_vec f = (\<chi> i. f i)" 

definition strategy_vectors :: "('strategy^'player) set"
  where "strategy_vectors = {s. \<forall>i. s$i \<in> possible_strategies i}"

definition payoff :: "'strategy^'player \<Rightarrow> 'player \<Rightarrow> 'payoff" 
  where "payoff s i = (payoffs s)$i"

lemma strategy_vector_iff_fun:
  fixes s :: "'strategy^'player"
  shows "(s \<in> strategy_vectors) = (\<exists>f. (s = fun_to_vec f \<and> f \<in> strategy_funs))"
proof - 
  have "(s \<in> strategy_vectors) = (\<forall>i. s$i \<in> possible_strategies i)" 
    by (simp add: strategy_vectors_def) 
  hence "(s \<in> strategy_vectors) = (\<exists>f. (s = fun_to_vec f \<and> (\<forall>i. f i \<in> possible_strategies i)))"
    using fun_to_vec_def vec_lambda_beta vec_lambda_eta by metis 
  thus ?thesis
    by (simp add: strategy_funs_def) 
qed

text "We prove the existence of legal plays, both as functions from players to strategies, and as 
player-indexed vectors of strategies. In particular, legal plays exist that include any particular
choice of strategy for any player."

lemma strategy_fun_fix_exists: 
  fixes s\<^sub>i :: "'strategy" 
  assumes fixed_strategy:  "s\<^sub>i \<in> possible_strategies i" 
  shows "\<exists>f. f \<in> strategy_funs \<and> f i = s\<^sub>i"
proof -
  let ?s' = "(\<lambda>j. (if j = i then s\<^sub>i else (SOME s. s \<in> possible_strategies j)))" 
  have "\<forall>i. ?s' i \<in> (possible_strategies i)"
    by (simp add: players_can_play some_in_eq fixed_strategy) 
  hence "?s' \<in> strategy_funs"
    using strategy_funs_def by simp 
  thus ?thesis 
    by auto 
qed

lemma strategy_fun_exists: "\<exists>f. f \<in> strategy_funs"
  using strategy_fun_fix_exists players_have_a_move by blast 

lemma strategy_vector_fix_exists: 
  fixes s\<^sub>i :: "'strategy" 
  assumes fixed_strategy:  "s\<^sub>i \<in> possible_strategies i" 
  shows "\<exists>s. s \<in> strategy_vectors \<and> s$i = s\<^sub>i" 
proof - 
  obtain f where "f \<in> strategy_funs \<and> f i = s\<^sub>i"
    using fixed_strategy strategy_fun_fix_exists by auto 
  hence "(fun_to_vec f) \<in> strategy_vectors \<and> (fun_to_vec f)$i = s\<^sub>i"
    by (simp add: fun_to_vec_def strategy_vector_iff_fun)
  thus ?thesis 
    by auto 
qed

lemma strategy_vector_exists: "\<exists>s. s \<in> strategy_vectors" 
  using strategy_vector_fix_exists players_have_a_move by blast 

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
    by (simp add: strategy_vectors_def)
  hence "((s\<^sub>i,s\<^sub>-\<^sub>i) \<in> strategy_vectors) = (((s\<^sub>i,s\<^sub>-\<^sub>i)$i \<in> possible_strategies i) \<and>
         (\<forall>j. ((j \<noteq> i) \<longrightarrow> (s\<^sub>i,s\<^sub>-\<^sub>i)$j \<in> possible_strategies j)))"
    by auto
  thus ?thesis
    by (simp add: player_chooses_completion completion_fixes_other_players)
qed

lemma completion_of_legal_play: 
    fixes s :: "'strategy^'player"
  assumes legal_play: "s \<in> strategy_vectors"
    shows "(s\<^sub>i,s\<^sub>-\<^sub>i) \<in> strategy_vectors = (s\<^sub>i \<in> possible_strategies i)"
  using completion_legal_iff legal_play strategy_vectors_def by auto

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