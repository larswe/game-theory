theory Game_Theory 
  imports "HOL-Analysis.Analysis"
begin

locale strategic_game = 
  fixes number_of_players :: "nat" 
    and strategies :: "nat \<Rightarrow> 'strategy"
begin

abbreviation "n == number_of_players"

(* Note 0-indexation. *)
definition players :: "nat set" 
  where "players = {i . i < n}"

lemma n_is_card: "n = card players"
  by (simp add: players_def) 


end

end