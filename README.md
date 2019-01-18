# Synquid_plus

関数型プログラム合成ツールです。
詳細型(refinemete type)を入力として受け取り、それに対応する関数型プログラムを合成します。
Synquidという既存ツールを拡張（利用）する形で、補助関数付きプログラムの合成を行います。

既存手法
https://bitbucket.org/nadiapolikarpova/synquid


## デモ

http://www.kb.is.s.u-tokyo.ac.jp/~eguchi/tools/aplas18/


## 入出力
Synquidと同じです。


## 構成
以下の３ステップからなります。

 1.合成目標の型から、再帰関数のテンプレートを作成

 2.テンプレート中の、未知の補助関数の型を推論

 3.推論した型をSynquidに渡すことで、目標の関数を合成
