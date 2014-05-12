# Shatranj

Shatranj is an bitboard-based, Open-Source, interactive chess programming module which allows manipulation of chess positions and experimentation with search algorithms and evaluation techniques. The project goal is to write a toolkit to aid in implementing Shannon Type B chess programs. As such, execution speed becomes less important then code clarity and expressive power of the implementation language. Having been written in an interpreted language, this module allows the chess programmer to manipulate bitboards in a natural, interactive manner much like signal processing toolkits allow communication engineers to manipulate vectors of sounds samples in MATLAB. The module currenly implements a simple recursive minimax search with alphabeta pruning, iterative deepening, uses short algebraic notation, handles repetition check, and the 50 move rule. Features lacking are quiescent checks, transition tables, negascout and MTD searching.

This toolkit is available in the form of a Python module called shatranj.py. You will also likely need the opening book as well as some of the pre-built hash tables that are used throughout the module (these will be recalculated if the module cannot find the data file). Place all three files in the same directory and simply run python on the python module ("python shatranj.py"). As far as requirements, all that is needed is a recent version of the interpreted, high level language called Python (anything after version 2.3 should work fine).

Shatranj will also work as a chess engine with GUIs such as Xboard and Winboard. Both are free and and available from Tim Mann's Chess pages in the previous link. Simply send Shatranj a command line option "-xboard". For example, with Xboard, one can use the following to play against Shatranj:

xboard -debug -size medium -fcp "/sw/bin/python -u shatranj.py -xboard "

(Note: for this to work, you need to be in the same directory as where shatranj was installed (shatranj.py, shatranj-book.bin, and shatranj-data.bin). You may also need to change the path to your python executable.)

Winboard users can use the following text saved in a batch file (kindly provided by Eber Ramirez) making sure to leave the quotes in:

"c:\winboard-4.2.7\winboard" -debug -size medium -fcp "c:\python25\python -u c:\shatranj\shatranj.py -xboard "

(Note: again, you'll need to change the paths to where you installed python, winboard and shatranj. You can either type this into a shell (DOS window) or save it as a batch file and create a shortcut to this file.)

Until more documentation becomes available, here is a short paper (PDF) that explains the move generation (from the ICGA Journal Vol. 30 No.2) which is in this same repository.

	And here is a sample session:
	[Sam-Tannous-Computer:~/shatranj] stannous% python
	>>> from shatranj import *
	...reading startup data
	...total time to read data 0.0774528980255
	...found opening book shatranj-book.bin with 37848 positions
	>>> position = Position("r1bqk2r/pppp1ppp/2n5/5N2/2B1n3/8/PPP1QPPP/R1B1K2R")
	>>> all_pieces = position.piece_bb["b_occupied"] | position.piece_bb["w_occupied"]
	>>> other_pieces = position.piece_bb["b_occupied"]
	>>> from_square = c4
	>>> wtm = 1
	>>> mask = position.pinned(from_square,wtm)
	>>> ne_pieces = diag_mask_ne[from_square] & all_pieces
	>>> nw_pieces = diag_mask_nw[from_square] & all_pieces
	>>> moves = ((diag_attacks_ne[from_square][ne_pieces] & other_pieces) | \
	...          (diag_attacks_ne[from_square][ne_pieces] & ~all_pieces)  | \
	...          (diag_attacks_nw[from_square][nw_pieces] & other_pieces) | \
	...          (diag_attacks_nw[from_square][nw_pieces] & ~all_pieces)) & mask
	>>> 
	>>> moves
	1275777090846720L
	>>> 
	>>> tobase(moves,2)
	'100100010000101000000000000010100000000000000000000'
	>>> display(moves)

	    +---+---+---+---+---+---+---+---+
	  8 |   | . |   | . |   | . |   | . | 
	    +---+---+---+---+---+---+---+---+
	  7 | . |   | . |   | . | 1 | . |   | 
	    +---+---+---+---+---+---+---+---+
	  6 | 1 | . |   | . | 1 | . |   | . | 
	    +---+---+---+---+---+---+---+---+
	  5 | . | 1 | . | 1 | . |   | . |   | 
	    +---+---+---+---+---+---+---+---+
	  4 |   | . |   | . |   | . |   | . | 
	    +---+---+---+---+---+---+---+---+
	  3 | . | 1 | . | 1 | . |   | . |   | 
	    +---+---+---+---+---+---+---+---+
	  2 |   | . |   | . |   | . |   | . | 
	    +---+---+---+---+---+---+---+---+
	  1 | . |   | . |   | . |   | . |   | 
	    +---+---+---+---+---+---+---+---+
	      a   b   c   d   e   f   g   h  

	>>> position.show_moves(1)
	['Rg1', 'O-O', 'f3', 'a3', 'Rb1', 'f4', 'Ba6', 
	'Bh6', 'Bd3', 'Qg4', 'Qe3', 'Ne7', 'Be6', 'Nxg7', 
	'Qxe4', 'Ne3', 'b4', 'Nh4', 'b3', 'Be3', 'Bg5', 
	'g3', 'Kf1', 'Rf1', 'Nh6', 'a4', 'Ng3', 'Qh5', 
	'Kd1', 'h4', 'h3', 'c3', 'Bxf7', 'Nd6', 'Bb5', 
	'Nd4', 'Qf3', 'g4', 'Qf1', 'Bb3', 'Qd1', 'Qd3', 
	'Qd2', 'Bd5', 'Bd2', 'Bf4']
	>>> 
	>>> # now play a game!
	>>> play()
	Shatranj version 1.10
	         g: switch sides     m: show legal moves
	         n: new game         l: list game record
	         d: display board    b: show book moves
	        sd: change search depth (2-16) default=5
	         q: quit

	Shatranj: d

	    +---+---+---+---+---+---+---+---+
	  8 | r | n | b | q | k | b | n | r | 
	    +---+---+---+---+---+---+---+---+
	  7 | p | p | p | p | p | p | p | p | 
	    +---+---+---+---+---+---+---+---+
	  6 |   | . |   | . |   | . |   | . | 
	    +---+---+---+---+---+---+---+---+
	  5 | . |   | . |   | . |   | . |   | 
	    +---+---+---+---+---+---+---+---+
	  4 |   | . |   | . |   | . |   | . | 
	    +---+---+---+---+---+---+---+---+
	  3 | . |   | . |   | . |   | . |   | 
	    +---+---+---+---+---+---+---+---+
	  2 | P | P | P | P | P | P | P | P | 
	    +---+---+---+---+---+---+---+---+
	  1 | R | N | B | Q | K | B | N | R | 
	    +---+---+---+---+---+---+---+---+
	      a   b   c   d   e   f   g   h  



	Shatranj: 
