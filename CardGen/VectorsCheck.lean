import CardGen.Vectors

/-! 書き出したテストベクトルが古くないかの確認（検査ツール自体はこのファイルを読まない） -/

namespace CardGen

-- `csharp/vectors.json` は、ここで作るテストベクトルと同じ内容（Lean の定義を変えたら書き出し直す）
#guard_msgs in
#eval show IO Unit from do
  let s ← IO.FS.readFile "csharp/vectors.json"
  unless s == vectors.pretty ++ "\n" do
    throw (IO.userError "csharp/vectors.json が古いです。lake exe cardgen --vectors csharp/vectors.json で書き出し直してください")

end CardGen
