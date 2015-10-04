(** %
\section{このライブラリについて}
\begin{screen}
\begin{itemize}
 \item このライブラリは河原康雄先生の ``関係の理論 - Dedekind 圏概説 -'' をもとに制作されている.
 \item 現状サポートしているのは,
 \begin{itemize}
  \item 1.4 節大半, 1.5 - 1.6 節全部
  \item 2.1 - 2.3 節全部, 2.4 - 2.5 節大半, 2.6 節全部, 2.7 節大半, 2.8 節有理性
  \item 4.2 - 4.3 節全部, 4.4 - 4.5 節大半, 4.6 節命題 4.6.1, 4.7 節大半
  \item 4.8 節は部分域公理を用いるので, そちらが終わり次第
 \end{itemize}
 といったところである.
 \item 関係論で話を進めたい場合は, 下の行に \verb|Require Export Basic_Notations_Rel.| を, 集合論で話を進めたい場合は, \verb|Require Export Basic_Notations_Set.| を記述する.
\end{itemize}
\end{screen}
% **)

Require Export Basic_Notations_Rel.

(** %
\begin{screen}
なお, 証明の書き方が悪いと, まれに ``関係論では証明が通ったのに, 集合論では通らない'' といったことも起こるようなので, ある程度注意しておく必要がある.
\end{screen}
% **)