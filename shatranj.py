#!/usr/bin/env python 

import string,time,random,cPickle,bisect,profile
import sys,select,types,math
try:
    import signal
except:
    pass

VERSION = "1.18"

'''
    Last Modified: May 12, 2014

    Shatranj is a bitboard based chess programming toolkit and engine.         
    Copyright (C) 2006-2014 Sam Tannous

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    This program may not be used in whole, nor in part, to enter
    any computer chess competition without written permission from
    the author.  Such permission will include the requirement that
    the program be entered under the name "Shatranj" so that   
    the program ancestry will be known.                                       
                                                                                
    Personal use does not allow anyone to enter this into a chess    
    tournament where other program authors are invited to participate.  You     
    can do your own local tournament, with Shatranj and other programs, since   
    this is for your personal enjoyment.  But you may not enter Shatranj into an  
    event where it will be in competition with other programs/programmers       
    without permission from the author.

    
    version  date        description                                            
    --------------------------------------------------------------------------- 
    1.00     12/10/2006  First OO version of the bit-board program to play      
                         a legitimate game
    1.10     04/06/2007  Some optimizations, and some other minor changes.
    1.11     04/06/2007  Fixed crash in en passant move generation, implemented
                         move take back.
    1.12     05/02/2007  Fixed bug in move generation.
    1.13     06/20/2007  Added ICGA Journal Article test code.
    1.15     11/28/2007  Added xboard compatibility mode.
    1.16     05/01/2008  Added support for Windows by catching lack of
                         signal support (thanks to Eber Ramirez).
    1.17     05/08/2008  Added some command-line features to set board position,
    1.18     05/12/2014  Remove psyco module since it is dead.
'''
class Move:
    def __init__(self,from_square,to_square,move_name="",
                 captured_piece="",promoted_piece=""):
        self.from_square = from_square
        self.to_square = to_square
        self.move_name = move_name
        self.captured_piece = captured_piece
        self.promoted_piece = promoted_piece

    def __repr__(self):
        print "Move: from square = %s  to square = %s  name = %s" % \
              (bin2alg[self.from_square],bin2alg[self.to_square],self.move_name)
        print "       captured piece = %s  promoted piece = %s" % \
              (str(self.captured_piece),str(self.promoted_piece))

        return("")
        
class Position:
    def __init__(self,fen=None):
        if (not fen):
            fen = INIT_FEN
        self.piece_bb = dict(w_occupied=0,
                             b_occupied=0,
                             P=0,N=0,B=0,R=0,Q=0,K=0,
                             p=0,n=0,b=0,r=0,q=0,k=0)
        self.piece_count = dict(P=0,N=0,B=0,R=0,Q=0,K=0,
                                p=0,n=0,b=0,r=0,q=0,k=0)

        self.piece_name = {}
        self.moves = {}
        self.attacks_from = {}
        self.attacks_to = {}
        for i in range(64):
            self.attacks_from[1L<<i] = 0
            self.attacks_to[1L<<i] = 0
        self.attacks_to[0] = 0
        self.attacks_from[0] = 0 
        self.move_history = []
        self.best_moves = []
        self.move_count = 0
        self.winner = None
        self.in_check = 0
        # castling checks
        self.w_king_move_count = 0
        self.b_king_move_count = 0
        self.w_rook_a1_move_count = 0
        self.w_rook_a1_location = a1
        self.w_rook_h1_move_count = 0
        self.w_rook_h1_location = h1
        self.b_rook_h8_move_count = 0
        self.b_rook_h8_location = h8
        self.b_rook_a8_move_count = 0
        self.b_rook_a8_location = a8
        # for en passant checks
        # last double pawn move is eligable for
        # capture if we are on the 5th rank (for white)
        # but it has to be captured on very next move
        # save the end square of the last double move
        self.w_pawn_last_double_move = 0
        self.b_pawn_last_double_move = 0
        # for 50 move rule
        # someone must have moved a pawn or made a capture
        # within the last 50 moves or the game is a draw
        self.half_move_counter = 0
        # Hash Index
        # ==========
        # The hash index is a FEN-like list made up of 
        # 1. 64 square content items (piece symbol or empty square '-',
        # 2. 1 side to move item ('wtm' for white, 'btm' for black to move),
        # 3. 1 item for castling ability ('-' for none, KQkq for
        #    respective sides,
        # 4. En Passant target square ('-' for none or the square behind
        #    the last two square pawn move),
        # 5. the half move counter: the number of half moves since the last
        #    pawn advance or capture -- for the 50 move rule.
        # 6. fullmove counter: the number of full moves
        #
        # This has to be a list since arrays are not order dependent.
        # It is 69 items long.  The following variables are used to access
        # these locations:
        # MOVER_HASH_INDEX = 64
        # CASTLING_HASH_INDEX = 65
        # ENPASSANT_HASH_INDEX = 66
        # HALF_MOVE_HASH_INDEX = 67
        # FULL_MOVE_HASH_INDEX = 68

        self.hash_index = ['-']*64 + ['wtm'] + ['KQkq'] + ['-'] + [0] + [0]

        # we also track the half moves in a list so we can backtrack if needed.
        # this needs to be a list because in a search, we might have to take
        # back a move where the half move counter was 0 and we need to know
        # where the counter was before it was reset to 0 because of a pawn
        # move or a capture.
        # This is just a running counter of half moves that gets reset
        # when there is a pawn move or capture.
        #  [0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7]
        #                  ^           ^------ pawn moves or captures          
        self.half_move_counter_list = [0]

        # we need to keep track of positions we've seen so we can detect
        # repititions.  we track this with an array that uses the hash_index
        # of the position and keeps track of how many times we have seen
        # this position. 
        # This is simply a list of the state of the position counters for each move
        # [{position_counters move 0}, {position_counters move 1}, ...]
        self.position_counter_array_list = [{}]

        row = fen.split("/")
        index = 63
        self.fen = fen
        for i in row:
            for j in i:
                if (j in "12345678"): # we have a space, move the index
                    index -= int(j)
                else:  # we have a piece
                    self.piece_bb[j] |= 1L<<index
                    self.piece_name[1L<<index] = j
                    self.piece_count[j] += 1
                    index -= 1

        # Initialize the hash index for the transition tables
        for i in range(64):
            if (self.piece_name.has_key(1L<<i)):
                self.hash_index[i] = self.piece_name[1L<<i]
            else:
                self.hash_index[i] = '-'

        self.piece_bb['w_occupied'] = self.piece_bb['P'] | self.piece_bb['R'] | \
                                      self.piece_bb['N'] | self.piece_bb['B'] | \
                                      self.piece_bb['Q'] | self.piece_bb['K']
        self.piece_bb['b_occupied'] = self.piece_bb['p'] | self.piece_bb['r'] | \
                                      self.piece_bb['n'] | self.piece_bb['b'] | \
                                      self.piece_bb['q'] | self.piece_bb['k']
        
    def __repr__(self):
        white = 1
        for r in range(8,0,-1):
            print "\n    +---+---+---+---+---+---+---+---+"
            print " ",r, "|",
            for f in "abcdefgh":
                name = "%s%s" % (f,r)
                bb = alg2bin[name]
                if (self.piece_name.has_key(bb)):
                    print self.piece_name[bb],"|",
                else:
                    if (white):
                        print " ","|",
                    else:
                        print ".","|",
                white ^= 1
            white ^= 1
        print "\n    +---+---+---+---+---+---+---+---+"
        print "      a   b   c   d   e   f   g   h  \n"
        return("")

    def generate_moves (self,wtm):
        """
        This generates all the legal moves.  First, we check
        to see if the king is in check.
        """
        piece_bb = self.piece_bb
        piece_name = self.piece_name
        move_list = []
        self.winner = None
        self.in_check = 0
        self.side_in_check = None

        # later on we need to update attacks in efficiently in
        # move() and unmove() but for now, we'll do it manually
        # for each move
        self.generate_attacks()
        attacks_from = self.attacks_from
        attacks_to = self.attacks_to

        if (wtm):
            other_pieces = piece_bb['b_occupied']
        else:
            other_pieces = piece_bb['w_occupied']

        all_pieces = piece_bb['b_occupied'] | piece_bb['w_occupied']

        if (wtm):
            king = piece_bb['K']
        else:
            king = piece_bb['k']

        # check to make sure we have a king.
        # If we don't, we shouldn't be here.
        if (king == 0):
            print "Error: one of the kings is missing."
            print self #display(position)
            sys.exit()
            return(([],[]))

        # Are we in check?! Check!!
        if (attacks_to[king] & other_pieces):        
            # we are in check, find check evasions to get out
            #print "generate_moves: In CHECK!"
            #print self
            self.in_check = 1
            self.side_in_check = wtm
            move_list = self.generate_check_evasions(wtm)

            if (not len(move_list)): 
                #print "generate_moves: no moves!"
                #print self
                # no moves...game is over :-(
                if (wtm):
                    self.winner = "black"
                else:
                    self.winner = "white"
                #print "winner is",self.winner
                return([])
            else:
                # only return moves that get us out of check
                return(move_list)

        # we're not in check, but we need to make sure
        # we don't cause a discovered check
        #
        # at this point we already know the attacks_from for all
        # pieces...we just need to remove our own pieces from the attack.
        if (wtm):
            pieces = piece_bb['w_occupied'] & ~piece_bb['P']
        else:
            pieces = piece_bb['b_occupied'] & ~piece_bb['p']

        kings = piece_bb['k'] | piece_bb['K']
        while (pieces):
            from_square = ((pieces) & -(pieces))
            mask = self.pinned(from_square,wtm)
            moves = (attacks_from[from_square] & (other_pieces | ~all_pieces)) & mask
            while (moves):
                to_square = ((moves) & -(moves))
                # need to make sure king doesn't move into check
                if ((from_square & kings) and \
                    (attacks_to[to_square] & other_pieces)):
                    pass
                elif (to_square & other_pieces):  # capture
                    move_list.insert(0,Move(from_square,to_square,"",
                                            piece_name[to_square],""))
                else:                             # empty square
                    move_list.append(Move(from_square,to_square,"","",""))            

                moves = ((moves) & ((moves) - 1L))

            pieces = ((pieces) & ((pieces) - 1L))

        # try to castle.  If the king was in check, the moves are generated
        # in the check_evasions routine above.
        w_occupied_ks = (g1 | f1) & all_pieces
        w_occupied_qs = (b1 | c1 | d1) & all_pieces
        b_occupied_ks = (g8 | f8) & all_pieces
        b_occupied_qs = (b8 | c8 | d8) & all_pieces
        if (wtm and piece_bb['K'] == e1 and \
            self.w_king_move_count == 0 and \
            (not w_occupied_ks or not w_occupied_qs)):
            piece = piece_bb['K']
            attacked_ks = (attacks_to[g1] | \
                           attacks_to[f1]) & other_pieces
            attacked_qs = (attacks_to[c1] | \
                           attacks_to[d1]) & other_pieces
            if (self.w_rook_h1_move_count == 0 and \
                piece_name.has_key(h1) and piece_name[h1] == 'R' and \
                not attacked_ks and not w_occupied_ks):
                move_list.append(Move(piece,g1,"castle","",""))

            if (self.w_rook_a1_move_count == 0 and \
                piece_name.has_key(a1) and piece_name[a1] == 'R' and \
                not attacked_qs and not w_occupied_qs):
                move_list.append(Move(piece,c1,"castle","",""))

        elif (not wtm and piece_bb['k'] == e8 and \
              self.b_king_move_count == 0 and \
              (not b_occupied_ks or not b_occupied_qs)):
            piece = piece_bb['k']
            attacked_ks = (attacks_to[g8] | \
                           attacks_to[f8]) & other_pieces
            attacked_qs = (attacks_to[c8] | \
                           attacks_to[d8]) & other_pieces
            if (self.b_rook_h8_move_count == 0 and \
                piece_name.has_key(h8) and piece_name[h8] == 'r' and \
                not attacked_ks and not b_occupied_ks):
                move_list.append(Move(piece,g8,"castle","",""))
            if (self.b_rook_a8_move_count == 0 and \
                piece_name.has_key(a8) and piece_name[a8] == 'r' and \
                not attacked_qs and not b_occupied_qs):
                move_list.append(Move(piece,c8,"castle","",""))

        # produce pawn captures
        # these are not handled in generate_attacks
        # since pawns can only attack diagonally (or enpassant) and pawns attack
        # empty square but moves can only take place if a piece exists on that square
        if (wtm):
            piece = piece_bb['P']
            left_captures  = piece<<9 & other_pieces & ~file_mask[h1] & ALL_ONES
            right_captures = piece<<7 & other_pieces & ~file_mask[a1] & ALL_ONES
        else:
            piece = piece_bb['p']
            left_captures  = piece>>7 & other_pieces & ~file_mask[h1]
            right_captures = piece>>9 & other_pieces & ~file_mask[a1]

        while (left_captures):
            to_square = ((left_captures) & -(left_captures))
            if (wtm): 
                from_square = to_square>>9 
            else:
                from_square = to_square<<7
            mask = self.pinned(from_square,wtm)
            if (mask & to_square):
                if (rank[to_square] == 8 or rank[to_square] == 1):
                    # promotion and capture
                    move_list.insert(0,Move(from_square,to_square,"promotion",
                                        piece_name[to_square],"Q"))
                else:
                    move_list.insert(0,Move(from_square,to_square,"",
                                        piece_name[to_square],""))
            left_captures = ((left_captures) & ((left_captures) - 1L))

        while (right_captures):
            to_square = ((right_captures) & -(right_captures))
            if (wtm): 
                from_square = to_square>>7 
            else:
                from_square = to_square<<9 & ALL_ONES
            mask = self.pinned(from_square,wtm)
            if (mask & to_square):
                if (rank[to_square] == 8 or rank[to_square] == 1):
                    # promotion and capture
                    move_list.insert(0,Move(from_square,to_square,"promotion",
                                        piece_name[to_square],"Q"))
                else:
                    move_list.insert(0,Move(from_square,to_square,"",
                                        piece_name[to_square],""))
            right_captures = ((right_captures) & ((right_captures) - 1L))

        # produce en passant captures
        if (wtm and self.b_pawn_last_double_move):
            last_double = self.b_pawn_last_double_move
            pawns = piece_bb['P']
            # handle the right side capture
            if (file[last_double] < 8):
                right_file = file_mask[last_double] >> 1
                rank5_pawn = pawns & rank_mask[a5] & right_file
                # there is a chance the pawn could be pinned along
                # a diagonal and could still capture en passant
                if (rank5_pawn):
                    mask = self.pinned(rank5_pawn,wtm)
                    to_square = file_mask[last_double] & rank_mask[a6]
                    if (mask & to_square):
                        move_list.insert(0,Move(rank5_pawn,to_square,"enpassant","p",""))
            # handle the left side capture
            if (file[last_double] > 1):
                left_file = file_mask[last_double] << 1
                rank5_pawn = pawns & rank_mask[a5] & left_file
                # there is a chance the pawn could be pinned along
                # a diagonal and could still capture en passant
                if (rank5_pawn):
                    mask = self.pinned(rank5_pawn,wtm)
                    to_square = file_mask[last_double] & rank_mask[a6]
                    if (mask & to_square):
                        move_list.insert(0,Move(rank5_pawn,to_square,"enpassant","p",""))
        elif (not wtm and self.w_pawn_last_double_move):
            last_double = self.w_pawn_last_double_move
            pawns = piece_bb['p']
            # handle the right side capture
            if (file[last_double] < 8):
                right_file = file_mask[last_double] >> 1
                rank4_pawn = pawns & rank_mask[a4] & right_file
                # there is a chance the pawn could be pinned along
                # a diagonal and could still capture en passant
                if (rank4_pawn):
                    mask = self.pinned(rank4_pawn,wtm)
                    to_square = file_mask[last_double] & rank_mask[a3]
                    if (mask & to_square):
                        move_list.insert(0,Move(rank4_pawn,to_square,"enpassant","P",""))
            # handle the left side capture
            if (file[last_double] > 1):
                left_file = file_mask[last_double] << 1
                rank4_pawn = pawns & rank_mask[a4] & left_file
                # there is a chance the pawn could be pinned along
                # a diagonal and could still capture en passant
                if (rank4_pawn):
                    mask = self.pinned(rank4_pawn,wtm)
                    to_square = file_mask[last_double] & rank_mask[a3]
                    if (mask & to_square):
                        move_list.insert(0,Move(rank4_pawn,to_square,"enpassant","P",""))

        # produce single pawn moves...these are not handled in generate_attacks
        # since pawns can only attack diagonally (or enpassant) and pawns attack
        # empty square but moves can only take place if a piece exists on that square
        if (wtm):
            piece = piece_bb['P']
            single_moves = piece<<8 & ~all_pieces
            double_moves = (single_moves<<8) & ~all_pieces & rank_mask[a4]
        else:
            piece = piece_bb['p']
            single_moves = piece>>8 & ~all_pieces    
            double_moves = (single_moves>>8) & ~all_pieces & rank_mask[a5]
        while (single_moves):
            to_square = ((single_moves) & -(single_moves))
            if (wtm):
                from_square = to_square>>8
            else:
                from_square = to_square<<8
            mask = self.pinned(from_square,wtm)
            if (mask & to_square):
                if (rank[to_square] == 8 or rank[to_square] == 1):
                    move_list.append(Move(from_square,to_square,"promotion","","Q"))
                else:
                    move_list.append(Move(from_square,to_square,"","",""))
            single_moves = ((single_moves) & ((single_moves) - 1L))

        # produce double pawn moves
        while (double_moves):
            to_square = ((double_moves) & -(double_moves))
            if (wtm):
                from_square = to_square>>16
            else:
                from_square = to_square<<16
            mask = self.pinned(from_square,wtm)
            if (mask & to_square):
                #print "WE ARE HERE",bin2alg[from_square]
                move_list.append(Move(from_square,to_square,"pawn double move","",""))
            double_moves = ((double_moves) & ((double_moves) - 1L))

        return(move_list)

    def show_moves (self,wtm):
        move_list = self.generate_moves(wtm)
        moves,san_moves = self.get_move_list(move_list)
        return(san_moves.values())

    def show_moves90 (self,wtm):
        move_list = self.generate_moves_rot(wtm)
        moves,san_moves = self.get_move_list(move_list)
        return(san_moves.values())

    def generate_moves_rot (self,wtm):
        """
        This generates all the legal moves.  First, we check
        to see if the king is in check.
        """
        piece_bb = self.piece_bb
        piece_name = self.piece_name
        move_list = []
        self.winner = None
        self.in_check = None
        self.side_in_check = None

        # later on we need to update attacks in efficiently in
        # move() and unmove() but for now, we'll do it manually
        # for each move
        self.generate_attacks()
        attacks_from = self.attacks_from
        attacks_to = self.attacks_to

        if (wtm):
            other_pieces = piece_bb['b_occupied']
        else:
            other_pieces = piece_bb['w_occupied']

        all_pieces = piece_bb['b_occupied'] | piece_bb['w_occupied']
        all_pieces90 = piece_bb['all_pieces90']
        all_pieces45ne = piece_bb['all_pieces45ne']
        all_pieces45nw = piece_bb['all_pieces45nw']

        if (wtm):
            king = piece_bb['K']
        else:
            king = piece_bb['k']

        # check to make sure we have a king.
        # If we don't, we shouldn't be here.
        if (king == 0):
            print "Error: one of the kings is missing."
            print self #display(position)
            sys.exit()
            return(([],[]))

        # Are we in check?! Check!!
        if (attacks_to[king] & other_pieces):        
            # we are in check, find check evasions to get out
            #print "In CHECK!"
            #display(position)
            self.in_check = 1
            self.in_check = wtm
            move_list = self.generate_check_evasions(wtm)

            if (not len(move_list)): 
                # no moves...game is over :-(
                if (wtm):
                    self.winner = "black"
                else:
                    self.winner = "white"

                return([])
            else:
                # only return moves that get us out of check
                return(move_list)

        # we're not in check, but we need to make sure
        # we don't cause a discovered check
        #
        # produce king and knight moves
        # we're not in check, but we need to make sure
        # we don't cause a discovered check
        #
        if (wtm):
            piece = piece_bb['K'] | piece_bb['N']  
        else:
            piece = piece_bb['k'] | piece_bb['n']
        knights = piece_bb['n'] | piece_bb['N']
        kings = piece_bb['k'] | piece_bb['K']

        while (piece):
            from_square = lsb(piece)
            mask = self.pinned(from_square,wtm)
            moves = ((king_moves[from_square & kings]   & other_pieces) | \
                     (king_moves[from_square & kings]   & ~all_pieces)  | \
                     (knight_moves[from_square & knights] & other_pieces) | \
                     (knight_moves[from_square & knights] & ~all_pieces)) & mask
            while (moves):
                to_square = lsb(moves)
                # need to make sure king doesn't move into check
                if ((from_square & kings) and \
                    (attacks_to[to_square] & other_pieces)):
                    pass
                elif (to_square & other_pieces):
                    move_list.insert(0,Move(from_square,to_square,"",piece_name[to_square],""))
                else:
                    move_list.append(Move(from_square,to_square,"","",""))            
                moves = clear_lsb(moves)
            piece = clear_lsb(piece)

        #################################################################
        # produce rook and queen moves
        if (wtm):
            piece = piece_bb['R'] | piece_bb['Q']
        else:
            piece = piece_bb['r'] | piece_bb['q']

        while (piece):
            moves = 0
            from_square = lsb(piece)
            mask = self.pinned(from_square,wtm)            
            # handle the rank attacks
            rank_shift = 8 * (rank[from_square] - 1) 
            first_rank_pieces = (all_pieces >> rank_shift) & 255

            file_shift = 8 * (rank[rot90[from_square]] - 1)
            first_file_pieces = (all_pieces90 >> file_shift) & 255

            # this produces all moves including our own piece attacks
            moves |= (RankAttacks[from_square][first_rank_pieces])
#                      ((other_pieces >> rank_shift) & 255) | \
##                      (RankAttacks[from_square][first_rank_pieces] & \
#                       ((~all_pieces >> rank_shift) & 255))) & mask

            moves |= (FileAttacks[from_square][first_file_pieces]) # & \
#                      ((other_pieces90 >> file_shift) & 255) | \
#                      (FileAttacks[from_square][first_file_pieces] & \
#                       ((~all_pieces90 >> file_shift) & 255))) & mask

            while (moves):
                to_square = lsb(moves)
                if (to_square & other_pieces):
                    move_list.insert(0,Move(from_square,to_square,"",piece_name[to_square],""))
                else:
                    move_list.append(Move(from_square,to_square,"","",""))            
                moves = clear_lsb(moves)
            piece = clear_lsb(piece)

        # produce bishop and queen moves
        if (wtm):
            piece = piece_bb['B'] | piece_bb['Q']
        else:
            piece = piece_bb['b'] | piece_bb['q']
        
        while (piece):
            moves = 0
            from_square = lsb(piece)
            mask = self.pinned(from_square,wtm)
            # handle the rank attacks
            ne_shift = 8 * (rank[rot45ne[from_square]] - 1) 
            ne_pieces = (all_pieces45ne >> ne_shift) & 255

            nw_shift = 8 * (rank[rot45nw[from_square]] - 1)
            nw_pieces = (all_pieces45nw >> nw_shift) & 255

            # this produces all moves including our own piece attacks
            moves |= (BishopAttacksNE[from_square][ne_pieces])
#                      ((other_pieces >> rank_shift) & 255) | \
##                      (RankAttacks[from_square][first_rank_pieces] & \
#                       ((~all_pieces >> rank_shift) & 255))) & mask

            moves |= (BishopAttacksNW[from_square][nw_pieces]) # & \
#                      ((other_pieces90 >> file_shift) & 255) | \
#                      (FileAttacks[from_square][first_file_pieces] & \
#                       ((~all_pieces90 >> file_shift) & 255))) & mask

            while (moves):
                to_square = lsb(moves)
                if (to_square & other_pieces):
                    move_list.insert(0,Move(from_square,to_square,"",piece_name[to_square],""))
                else:
                    move_list.append(Move(from_square,to_square,"","",""))            
                moves = clear_lsb(moves)
            piece = clear_lsb(piece)

        # try to castle.  If the king was in check, the moves are generated
        # in the check_evasions routine.
        w_occupied_ks = (g1 | f1) & all_pieces
        w_occupied_qs = (b1 | c1 | d1) & all_pieces
        b_occupied_ks = (g8 | f8) & all_pieces
        b_occupied_qs = (b8 | c8 | d8) & all_pieces
        if (wtm and piece_bb['K'] == e1 and \
            self.w_king_move_count == 0 and \
            (not w_occupied_ks or not w_occupied_qs)):
            piece = piece_bb['K']
            attacked_ks = (attacks_to[g1] | \
                           attacks_to[f1]) & other_pieces
            attacked_qs = (attacks_to[b1] | \
                           attacks_to[c1] |
                           attacks_to[d1]) & other_pieces
            if (self.w_rook_h1_move_count == 0 and \
                piece_name.has_key(h1) and piece_name[h1] == 'R' and \
                not attacked_ks and not w_occupied_ks):
                move_list.append(Move(piece,g1,"castle","",""))

            if (self.w_rook_a1_move_count == 0 and \
                piece_name.has_key(a1) and piece_name[a1] == 'R' and \
                not attacked_qs and not w_occupied_qs):
                move_list.append(Move(piece,c1,"castle","",""))

        elif (not wtm and piece_bb['k'] == e8 and \
              self.b_king_move_count == 0 and \
              (not b_occupied_ks or not b_occupied_qs)):
            piece = piece_bb['k']
            attacked_ks = (attacks_to[g8] | \
                           attacks_to[f8]) & other_pieces
            attacked_qs = (attacks_to[b8] | \
                           attacks_to[c8] |
                           attacks_to[d8]) & other_pieces
            if (self.b_rook_h8_move_count == 0 and \
                piece_name.has_key(h8) and piece_name[h8] == 'r' and \
                not attacked_ks and not b_occupied_ks):
                move_list.append(Move(piece,g8,"castle","",""))
            if (self.b_rook_a8_move_count == 0 and \
                piece_name.has_key(a8) and piece_name[a8] == 'r' and \
                not attacked_qs and not b_occupied_qs):
                move_list.append(Move(piece,c8,"castle","",""))

        # produce pawn captures
        if (wtm):
            piece = piece_bb['P']
            left_captures  = piece<<9 & other_pieces & ~file_mask[h1] & ALL_ONES
            right_captures = piece<<7 & other_pieces & ~file_mask[a1] & ALL_ONES
        else:
            piece = piece_bb['p']
            left_captures  = piece>>7 & other_pieces & ~file_mask[h1]
            right_captures = piece>>9 & other_pieces & ~file_mask[a1]
        while (left_captures):
            to_square = ((left_captures) & -(left_captures))
            if (wtm): 
                from_square = to_square>>9 
            else:
                from_square = to_square<<7
            mask = self.pinned(from_square,wtm)
            if (mask & to_square):
                if (rank[to_square] == 8 or rank[to_square] == 1):
                    # promotion and capture
                    move_list.insert(0,Move(from_square,to_square,"promotion",
                                        piece_name[to_square],"Q"))
                else:
                    move_list.insert(0,Move(from_square,to_square,"",
                                        piece_name[to_square],""))
            left_captures = ((left_captures) & ((left_captures) - 1L))

        while (right_captures):
            to_square = ((right_captures) & -(right_captures))
            if (wtm): 
                from_square = to_square>>7 
            else:
                from_square = to_square<<9 & ALL_ONES
            mask = self.pinned(from_square,wtm)
            if (mask & to_square):
                if (rank[to_square] == 8 or rank[to_square] == 1):
                    # promotion and capture
                    move_list.insert(0,Move(from_square,to_square,"promotion",
                                        piece_name[to_square],"Q"))
                else:
                    move_list.insert(0,Move(from_square,to_square,"",
                                        piece_name[to_square],""))
            right_captures = ((right_captures) & ((right_captures) - 1L))

        # produce en passant captures
        if (wtm and self.b_pawn_last_double_move):
            last_double = self.b_pawn_last_double_move
            pawns = piece_bb['P']
            # handle the right side capture
            if (file[last_double] < 8):
                right_file = file_mask[last_double] >> 1
                rank5_pawn = pawns & rank_mask[a5] & right_file
                # there is a chance the pawn could be pinned along
                # a diagonal and could still capture en passant
                if (rank5_pawn):
                    mask = self.pinned(rank5_pawn,wtm)
                    to_square = file_mask[last_double] & rank_mask[a6]
                    if (mask & to_square):
                        move_list.insert(0,Move(rank5_pawn,to_square,"enpassant","p",""))
            # handle the left side capture
            if (file[last_double] > 1):
                left_file = file_mask[last_double] << 1
                rank5_pawn = pawns & rank_mask[a5] & left_file
                # there is a chance the pawn could be pinned along
                # a diagonal and could still capture en passant
                if (rank5_pawn):
                    mask = self.pinned(rank5_pawn,wtm)
                    to_square = file_mask[last_double] & rank_mask[a6]
                    if (mask & to_square):
                        move_list.insert(0,Move(rank5_pawn,to_square,"enpassant","p",""))
        elif (not wtm and self.w_pawn_last_double_move):
            last_double = self.w_pawn_last_double_move
            pawns = piece_bb['p']
            # handle the right side capture
            if (file[last_double] < 8):
                right_file = file_mask[last_double] >> 1
                rank4_pawn = pawns & rank_mask[a4] & right_file
                # there is a chance the pawn could be pinned along
                # a diagonal and could still capture en passant
                if (rank4_pawn and (mask & to_square)):
                    mask = self.pinned(rank4_pawn,wtm)
                    to_square = file_mask[last_double] & rank_mask[a3]
                    if (mask & to_square):
                        move_list.insert(0,Move(rank4_pawn,to_square,"enpassant","P",""))
            # handle the left side capture
            if (file[last_double] > 1):
                left_file = file_mask[last_double] << 1
                rank4_pawn = pawns & rank_mask[a4] & left_file
                # there is a chance the pawn could be pinned along
                # a diagonal and could still capture en passant
                if (rank4_pawn):
                    mask = self.pinned(rank4_pawn,wtm)
                    to_square = file_mask[last_double] & rank_mask[a3]
                    if (mask & to_square):
                        move_list.insert(0,Move(rank4_pawn,to_square,"enpassant","P",""))

        # produce single pawn moves
        if (wtm):
            piece = piece_bb['P']
            single_moves = piece<<8 & ~all_pieces
            double_moves = (single_moves<<8) & ~all_pieces & rank_mask[a4]
        else:
            piece = piece_bb['p']
            single_moves = piece>>8 & ~all_pieces    
            double_moves = (single_moves>>8) & ~all_pieces & rank_mask[a5]
        while (single_moves):
            to_square = ((single_moves) & -(single_moves))
            if (wtm):
                from_square = to_square>>8
            else:
                from_square = to_square<<8
            mask = self.pinned(from_square,wtm)
            if (mask & to_square):
                if (rank[to_square] == 8 or rank[to_square] == 1):
                    move_list.append(Move(from_square,to_square,"promotion","","Q"))
                else:
                    move_list.append(Move(from_square,to_square,"","",""))
            single_moves = ((single_moves) & ((single_moves) - 1L))

        # produce double pawn moves
        while (double_moves):
            to_square = ((double_moves) & -(double_moves))
            if (wtm):
                from_square = to_square>>16
            else:
                from_square = to_square<<16
            mask = self.pinned(from_square,wtm)
            if (mask & to_square):
                #print "WE ARE HERE",bin2alg[from_square]
                move_list.append(Move(from_square,to_square,"pawn double move","",""))
            double_moves = ((double_moves) & ((double_moves) - 1L))

        return(move_list)

    def generate_check_evasions (self,wtm):
        # this should only get called if we're in check
        piece_bb = self.piece_bb
        piece_name = self.piece_name
        attacks_from = self.attacks_from
        attacks_to = self.attacks_to
        move_list = []

        all_pieces = piece_bb['b_occupied'] | piece_bb['w_occupied']

        last_double = 0
        rank45_pawns = 0
        if (wtm):
            other_pieces = piece_bb['b_occupied']
            our_pieces = piece_bb['w_occupied']
            king = piece_bb['K']
            pawns = piece_bb['P']
            forward_pawns = (pawns << 8) & ALL_ONES
            double_forward_pawns = ((pawns & rank_mask[a2]) << 16) & ALL_ONES 
            last_double = self.b_pawn_last_double_move        
            # capture toward the left
            if (last_double and file[last_double] < 8):
                rank45_pawns = piece_bb['P'] & \
                                (rank_mask[a5] & (file_mask[last_double]>>1))
            # capture toward the right
            if (last_double and file[last_double] > 1):
                rank45_pawns = rank45_pawns | \
                               (piece_bb['P'] & \
                                (rank_mask[a5] & (file_mask[last_double]<<1)))

        else:
            other_pieces = piece_bb['w_occupied']
            our_pieces = piece_bb['b_occupied']
            king = piece_bb['k']
            pawns = piece_bb['p']
            forward_pawns = pawns >> 8
            double_forward_pawns = (pawns & rank_mask[a7]) >> 16
            last_double = self.w_pawn_last_double_move        
            if (last_double and file[last_double] < 8):
                rank45_pawns = piece_bb['p'] & \
                                (rank_mask[a4] & (file_mask[last_double]>>1))
            if (last_double and file[last_double] > 1):
                rank45_pawns = rank45_pawns | \
                               (piece_bb['p'] & \
                                (rank_mask[a4] & (file_mask[last_double]<<1)))


        all_pieces = piece_bb['b_occupied'] | piece_bb['w_occupied']

        # check to make sure we're in check
        king_attackers = attacks_to[king] & other_pieces
        if (not king_attackers):
            print "Error: we're not in check.  We shouldn't be here."
            return

        # Yikes! We're in check!
        # we either
        # 1. capture the attacking piece
        # 2. move out of the way or
        # 3. block its path

        num_attackers = ipc(king_attackers)
        ############################################################################
        # option 1 Capture
        ############################################################################
        if (num_attackers == 1):
            # one attacker so we can try to capture it
            # with a piece other then the king.
            # if there are two attackers, no point in capturing
            # one of then unless the king captures it (and it's
            # unprotected)...king captures are handled in part 2
            # pawns can capture the attacking piece in a normal fashion
            # and this is handled here.  In the rare case that a pawn
            # can capture en passant, this is also handled here because
            # attacks_to should see this.
            attacker_attackers = attacks_to[king_attackers] & our_pieces & ~king
            while (attacker_attackers):
                attacker = ((attacker_attackers)   & -(attacker_attackers)  )
                # for en passant moves, we mask against the diag not the attacker
                # since that's where we end up.
                # a rank45 pawn can capture the threatening pawn en passant
                # first we determine the mask if we can capture en passant.
                # we check to make sure the attacker is the last pawn to move
                # a double move.
                mask = self.pinned(attacker,wtm)
                # make sure the attacker isn't pinned
                if (king_attackers & mask): 
                    # we handle the king attacks later
                    # handle the en passant move first
                    # the attacker must be the one doing en passant capture
                    # and the king attacker must be the one being captured
                    if (wtm):
                        if ((king_attackers & last_double) and (attacker & rank45_pawns)):
                            # wtm and enpassant
                            move_list.insert(0,Move(attacker,last_double<<8,
                                                    "enpassant","p",""))

                        elif (piece_name[attacker] == 'P' and rank[king_attackers] == 8):
                            # wtm and promotion along with the capture
                            move_list.insert(0,Move(attacker,king_attackers,"promotion",
                                                    piece_name[king_attackers],"Q"))
                        else:
                            move_list.insert(0,Move(attacker,king_attackers,"",
                                                    piece_name[king_attackers],""))
                    else:
                        if ((king_attackers & last_double) and (attacker & rank45_pawns)):
                            # not wtm and enpassant
                            move_list.insert(0,Move(attacker,last_double>>8,
                                                    "enpassant","P",""))                    
                        elif (piece_name[attacker] == 'p' and rank[king_attackers] == 1):
                            # not wtm and promotion along with the capture
                            move_list.insert(0,Move(attacker,king_attackers,"promotion",
                                                    piece_name[king_attackers],"Q"))
                        else:
                            move_list.insert(0,Move(attacker,king_attackers,"",
                                                    piece_name[king_attackers],""))

                attacker_attackers = ((attacker_attackers) & ((attacker_attackers) - 1L))


        ############################################################################
        # option 2 Move out of the way
        ############################################################################
        # move the king out of the way...ok to capture other pieces
        # or even the attacker (all the better)
        # captures and empty squares are found on the next line.
        moves = (king_moves[king] & other_pieces) | \
                (king_moves[king] & ~all_pieces)

        # eliminate sliding moves where we're still in check
        # we want to make sure we're not sliding
        # the king away from the attackers on the same
        # file, rank or diagonal....since we'd still be in
        # check....unless we take the piece attacking the king
        attackers = king_attackers
        king_rank_mask = rank_mask[king]
        king_file_mask = file_mask[king]
        king_diag_ne = diag_mask_ne[king]
        king_diag_nw = diag_mask_nw[king]
        attacker_masks = 0
        while (attackers):
            attacker = ((attackers) & -(attackers))
            name = piece_name[attacker]
            if (name in "QqRrBb"):
                # here, we keep a mask of all the attackers ranks
                # files and diagonals
                if (king_rank_mask == rank_mask[attacker]):
                    attacker_masks |= king_rank_mask
                elif (king_file_mask == file_mask[attacker]):
                    attacker_masks |= king_file_mask
                elif (king_diag_ne == diag_mask_ne[attacker]):
                    attacker_masks |= king_diag_ne
                elif (king_diag_nw == diag_mask_nw[attacker]):
                    attacker_masks |= king_diag_nw

            attackers = ((attackers) & ((attackers) - 1L))

        while (moves):
            to_square = ((moves) & -(moves))
            # find king's attackers if they exist...making sure the attacker
            # isn't protected if we take it.  If we are capturing a piece
            # we need to make sure the move goes off the attack file,
            # rank or diagonal.
            attacked_square = attacks_to[to_square] & other_pieces
            # To capture a piece it must
            # 1. be an opponent piece,
            # 2. not be protected (we can't move into check)
            # 3 a. If we're taking a piece on the attack rank, file
            #          or diagonal it had better be the one attacking
            #          the king since we can't stay in check.
            # 3 b. Or if it's not on the attack rank, file or diagonal,
            #          it can be any piece.
            if ((to_square & other_pieces) and \
                not attacked_square and \
                ((to_square & attacker_masks & king_attackers) or \
                 (to_square & ~attacker_masks))):
                move_list.insert(0,Move(king,to_square,"",piece_name[to_square],""))
            # the king can move to a empty non attacked square
            # but he can't stay on the same file, rank,
            # or diagonal of the attacker
            elif (to_square and not attacked_square and \
                  (to_square & attacker_masks == 0)):
                move_list.append(Move(king,to_square,"","",""))            

            moves = ((moves) & ((moves) - 1L))
        ############################################################################
        # option 3 Block
        ############################################################################
        if (num_attackers == 1):
            # if there is only one attacker, we can try 
            # blocking...we need to find the empty squares
            # between the king and the attacker on the file,
            # rank, or diagonal.  If there is more then one attacker
            # we can't really block them with one move...tough luck.
            if (rank[king] == rank[king_attackers]):
                rank_pieces = rank_mask[king] & all_pieces
                # this gives us empty squares
                moves = rank_attacks[king][rank_pieces] & ~all_pieces & \
                        rank_attacks[king_attackers][rank_pieces]
            elif (file[king] == file[king_attackers]): 
                file_pieces = file_mask[king] & all_pieces
                # this gives us empty squares
                moves = file_attacks[king][file_pieces] & ~all_pieces & \
                        file_attacks[king_attackers][file_pieces] 
            elif (diag_mask_ne[king] == diag_mask_ne[king_attackers]):
                ne_pieces = diag_mask_ne[king] & all_pieces
                # this gives us empty squares
                moves = diag_attacks_ne[king][ne_pieces] & ~all_pieces & \
                        diag_attacks_ne[king_attackers][ne_pieces] 
            elif (diag_mask_nw[king] == diag_mask_nw[king_attackers]):
                nw_pieces = diag_mask_nw[king] & all_pieces
                # this gives us empty squares
                moves = diag_attacks_nw[king][nw_pieces] & ~all_pieces & \
                        diag_attacks_nw[king_attackers][nw_pieces] 

            # we have all the empty squares so now we loop over them
            # and find all the pieces that can move there (attacks_to)
            # We have to take care here because pawns attack diagonally but
            # can't move there unless a piece is there to attack.  But
            # by now, we know all the squares are empty.
            # So we need to eliminate pawns as well as the king moving into
            # check.
            while (moves):
                empty_square = ((moves) & -(moves))
                blockers = attacks_to[empty_square] & ~pawns & \
                           ~king & ~other_pieces
                while (blockers):
                    blocker = ((blockers) & -(blockers))
                    mask = self.pinned(blocker,wtm)
                    if (mask & empty_square):
                        move_list.append(Move(blocker,empty_square,"","",""))
                    blockers = ((blockers) & ((blockers) - 1L))

                # find the forward pawn that sits on the empty square
                if (empty_square & forward_pawns):
                    #print "FOUND SINGLE"
                    blocking_pawn = empty_square & forward_pawns
                    if (wtm):
                        from_square = blocking_pawn>>8
                    else:
                        from_square = blocking_pawn<<8
                    mask = self.pinned(from_square,wtm)
                    if mask & empty_square:
                        if rank[empty_square] == 1 or rank[empty_square] == 8:
                            move_list.append(Move(from_square,empty_square,
                                                 "promotion","","Q"))
                        else:
                            move_list.append(Move(from_square,empty_square,
                                                 "","",""))
                elif (empty_square & double_forward_pawns):
                    # double moves for pawns must make sure that nothing
                    # is blocking their move to the empty square
                    blocking_pawn = empty_square & double_forward_pawns
                    if (wtm):
                        mask = self.pinned(blocking_pawn>>16,wtm)
                        if ((mask & empty_square) and \
                            ((empty_square >> 8) & ~all_pieces)):
                            move_list.append(Move(blocking_pawn >> 16,
                                                 empty_square,
                                                 "pawn double move","",""))
                    else:
                        mask = self.pinned(blocking_pawn<<16,wtm)
                        if ((mask & empty_square) and \
                            ((empty_square << 8) & ~all_pieces)):
                            move_list.append(Move(blocking_pawn << 16,
                                                 empty_square,
                                                 "pawn double move","",""))

                moves = ((moves) & ((moves) - 1L))

        return(move_list)

    def generate_attacks (self):
        """
        This generates the attacks_to and attacks_from arrays.
        """
        piece_bb = self.piece_bb
        piece_name = self.piece_name
        attacks_from = {}
        attacks_to = {}

        for i in range(64):
            attacks_from[1L<<i] = 0
            attacks_to[1L<<i] = 0

        all_pieces = piece_bb['b_occupied'] | piece_bb['w_occupied']

        #piece = piece_bb['K'] | piece_bb['N'] | piece_bb['k'] | piece_bb['n']
        knights = piece_bb['n'] | piece_bb['N']
        kings = piece_bb['k'] | piece_bb['K']
        queen_rooks = piece_bb['Q'] | piece_bb['q'] | piece_bb['R'] | piece_bb['r']
        queen_bishops = piece_bb['Q'] | piece_bb['q'] | piece_bb['B'] | piece_bb['b']

        non_pawns = all_pieces & ~piece_bb['P'] & ~piece_bb['p']
        
        while (non_pawns):
            from_square = ((non_pawns) & -(non_pawns))
            rank_pieces = rank_mask[from_square & queen_rooks] & all_pieces
            file_pieces = file_mask[from_square & queen_rooks] & all_pieces
            ne_pieces = diag_mask_ne[from_square & queen_bishops] & all_pieces
            nw_pieces = diag_mask_nw[from_square & queen_bishops] & all_pieces
            #wtm = from_square & piece_bb['w_occupied']
            #mask = self.pinned(from_square,wtm)
            moves = (king_moves[from_square & kings] | \
                     knight_moves[from_square & knights] | \
                     rank_attacks[from_square & queen_rooks][rank_pieces] | \
                     file_attacks[from_square & queen_rooks][file_pieces] | \
                     diag_attacks_ne[from_square & queen_bishops][ne_pieces] | \
                     diag_attacks_nw[from_square & queen_bishops][nw_pieces]) # & mask
            while (moves):
                to_square = ((moves) & -(moves))
                add_attacks(attacks_from,attacks_to,from_square,to_square)
                moves = ((moves) & ((moves) - 1L))

            non_pawns = ((non_pawns) & ((non_pawns) - 1L))

        # produce pawn attacks.  These are not necessarily moves since
        # a piece has to be there for the pawn to move there.
        for wtm in [0,1]:
            # in case we shift off the board (> 64 bits) we need to
            # mask our values with all ones to keep things sane.
            if (wtm):
                piece = piece_bb['P']
                left_captures  = piece<<9 & ~file_mask[h1] & ALL_ONES
                right_captures = piece<<7 & ~file_mask[a1] & ALL_ONES
            else:
                piece = piece_bb['p']
                left_captures  = piece>>7 & ~file_mask[h1]
                right_captures = piece>>9 & ~file_mask[a1]
            while (left_captures):
                to_square = ((left_captures) & -(left_captures))
                if (wtm): 
                    from_square = to_square>>9 
                else:
                    from_square = to_square<<7
                add_attacks(attacks_from,attacks_to,from_square,to_square)
                left_captures = ((left_captures) & ((left_captures) - 1L))
            while (right_captures):
                to_square = ((right_captures) & -(right_captures))
                if (wtm):
                    from_square = to_square>>7 
                else:
                    from_square = to_square<<9
                add_attacks(attacks_from,attacks_to,from_square,to_square)
                right_captures = ((right_captures) & ((right_captures) - 1L))

            # produce en passant attacks
            # for en passant, the pawn really doesn't attack the
            # squares diagonally on the side of the pawn that just moved
            # two squares forward.  It attacks the pawn directly next to it
            # (as well as the diagonal in front of it).
            if (wtm and self.b_pawn_last_double_move):
                pawns = piece_bb['P']
                double_pawn = self.b_pawn_last_double_move
                # handle the right side capture
                if (file[double_pawn] < 8):
                    right_file = file_mask[double_pawn] >> 1
                    rank5_pawn = pawns & rank_mask[a5] & right_file
                    if (rank5_pawn):
                        to_square = double_pawn 
                        add_attacks(attacks_from,attacks_to,rank5_pawn,to_square)

                # handle the left side capture
                if (file[double_pawn] > 1):
                    left_file = file_mask[double_pawn] << 1
                    rank5_pawn = pawns & rank_mask[a5] & left_file
                    if (rank5_pawn):
                        to_square = double_pawn
                        add_attacks(attacks_from,attacks_to,rank5_pawn,to_square)

            elif (not wtm and self.w_pawn_last_double_move):
                pawns = piece_bb['p']
                double_pawn = self.w_pawn_last_double_move
                # handle the right side capture
                if (file[double_pawn] < 8):
                    right_file = file_mask[double_pawn] >> 1
                    rank4_pawn = pawns & rank_mask[a4] & right_file
                    if (rank4_pawn):
                        to_square = double_pawn
                        add_attacks(attacks_from,attacks_to,rank4_pawn,to_square)

                # handle the left side capture
                if (file[double_pawn] > 1):
                    left_file = file_mask[double_pawn] << 1
                    rank4_pawn = pawns & rank_mask[a4] & left_file
                    if (rank4_pawn):
                        to_square = double_pawn 
                        add_attacks(attacks_from,attacks_to,rank4_pawn,to_square)

        self.attacks_from = attacks_from
        self.attacks_to = attacks_to
        return

    def pinned (self,square,wtm):
        """
        Determine if the piece on square is pinned to the king
        and return the BB mask we need to stay on if pinned.
        We need this since the pinned piece can still move along
        the rank/file/diagonal or even capture the pinner.
        Since the attackers that pin a piece must be the sliders
        such as rooks, bishops, and queens.
        """
        attacks_to = self.attacks_to
        piece_bb = self.piece_bb
        if (wtm):
            king = piece_bb["K"]
            other_pieces = piece_bb['b_occupied']
            sliders = piece_bb['r'] | piece_bb['b'] | piece_bb['q']
        else:
            king = piece_bb["k"]
            other_pieces = piece_bb['w_occupied']
            sliders = piece_bb['R'] | piece_bb['B'] | piece_bb['Q']

        all_pieces = piece_bb['b_occupied'] | piece_bb['w_occupied']
        # The attacker is on the same rank or file as the king and the
        # pinned piece.
        mask = ALL_ONES
        if (file_mask[square] & file_mask[king] & attacks_to[square] & other_pieces):
            # remove the square and see if the king is attacked
            attackers = file_mask[king] & attacks_to[square] & sliders
            while (attackers):
                attacker = ((attackers) & -(attackers))
                file_pieces = file_mask[king] & all_pieces & ~square
                if (file_attacks[attacker][file_pieces] & king):
                    mask = file_mask[king]
                attackers = ((attackers) & ((attackers) - 1L))

        elif (rank_mask[square] & rank_mask[king] & attacks_to[square] & other_pieces):
            # remove the square and see if the king is attacked
            attackers = rank_mask[king] & attacks_to[square] & sliders
            while (attackers):
                attacker = ((attackers) & -(attackers))
                rank_pieces = rank_mask[king] & all_pieces & ~square
                if (rank_attacks[attacker][rank_pieces] & king):
                    mask = rank_mask[king]
                attackers = ((attackers) & ((attackers) - 1L))

        # The attacker is on the same diagonal as the king and the
        # pinned piece.
        elif (diag_mask_ne[square] & diag_mask_ne[king] & attacks_to[square] & other_pieces):
            # remove the square and see if the king is attacked
            attackers = diag_mask_ne[king] & attacks_to[square] & sliders
            while (attackers):
                attacker = ((attackers) & -(attackers))
                ne_pieces = diag_mask_ne[king] & all_pieces & ~square
                if (diag_attacks_ne[attacker][ne_pieces] & king):
                    mask = diag_mask_ne[king]

                attackers = ((attackers) & ((attackers) - 1L))

        elif (diag_mask_nw[square] & diag_mask_nw[king] & attacks_to[square] & other_pieces):
            # remove the square and see if the king is attacked
            attackers = diag_mask_nw[king] & attacks_to[square] & sliders
            while (attackers):
                attacker = ((attackers) & -(attackers))
                nw_pieces = diag_mask_nw[king] & all_pieces & ~square
                if (diag_attacks_nw[attacker][nw_pieces] & king):
                    mask = diag_mask_nw[king]
                attackers = ((attackers) & ((attackers) - 1L))

        return(mask)

    def reg2san (self,move):
        # Convert from regular notation to
        # Short Algebraic Notation (SAN)
        piece_name = self.piece_name
        mover = piece_name[move.from_square].upper()
        # a capture move
        if (move.captured_piece != ""):
            if (mover == "P" or mover == "p"):
                san_move = bin2alg[move.from_square][0]
            else:
                san_move = mover
            san_move = "%sx%s" % (san_move,bin2alg[move.to_square])

        # handle a castle move
        elif (move.move_name == "castle"):
            if (move.to_square == g1 or move.to_square == g8):
                san_move = "O-O"
            else:
                san_move = "O-O-O" 

        # all other moves
        else:
            if (mover == "P" or mover == "p"):
                san_move = bin2alg[move.to_square]
            else:
                san_move = mover
                san_move = "%s%s" % (san_move,bin2alg[move.to_square])

        # handle promotion move
        if (move.move_name == "promotion"):
            # here we add on an = sign but this can be changed later
            san_move = "%s=" % (san_move)

        return(san_move)

    def get_move_list (self,move_list):
        """
        moves is an array with indicies of both regular moves (e2e4,b1c3) and
        san moves (e4,Nc3) that map to real move tuples (f,t,n,c,p).

        san_moves is an array that only maps regular moves (e2e4,b1c3)
        to san moves (e4,Nc3).

        san_moves
        c3e2 --> Ne2

        c3e2 --> Nce2
        g1e2 --> Nge2

        """
        moves = {}
        san_moves = {}
        for m in move_list:
            regular_move = "%s%s" % (bin2alg[m.from_square],bin2alg[m.to_square])
            moves[regular_move] = m
            san = self.reg2san(m)
            # check to see if we have a conflict
            if (moves.has_key(san)):
                old_move = moves[san]
                new_move = m
                old_from_square = old_move.from_square
                new_from_square = new_move.from_square
                old_reg_move = "%s%s" % (bin2alg[old_move.from_square],
                                         bin2alg[old_move.to_square])
                new_reg_move = "%s%s" % (bin2alg[new_move.from_square],
                                         bin2alg[new_move.to_square])
                # pieces are are different files so we use the file
                if (file[old_from_square] != file[new_from_square]):
                    old_file = bin2alg[old_from_square][0]
                    new_file = bin2alg[new_from_square][0]
                    old_san = "%s%s%s" % (san[0:1],old_file,san[1:])
                    new_san = "%s%s%s" % (san[0:1],new_file,san[1:])
                # pieces are on different ranks so we use the rank
                else:
                    old_rank = bin2alg[old_from_square][1]
                    new_rank = bin2alg[new_from_square][1]
                    old_san = "%s%s%s" % (san[0:1],old_rank,san[1:])
                    new_san = "%s%s%s" % (san[0:1],new_rank,san[1:])                

                del moves[san]
                san_moves[old_reg_move] = old_san
                san_moves[new_reg_move] = new_san
                moves[old_san] = old_move
                moves[new_san] = new_move

            else:
                moves[san] = m
                san_moves[regular_move] = san

        return(moves,san_moves)

    def make_move (self,move):
        piece_name = self.piece_name
        piece_bb = self.piece_bb
        piece_count = self.piece_count
        attacks_from = self.attacks_from
        attacks_to = self.attacks_to
        hash = self.hash_index
        from_square = move.from_square
        to_square = move.to_square
        move_name = move.move_name
        captured_piece = move.captured_piece
        promoted_piece = move.promoted_piece

        if (DEBUG_MOVES):
            print "make_move =",move
            
        from_piece = piece_name[from_square] # piece name

        all_pieces = piece_bb['b_occupied'] | piece_bb['w_occupied']

        if (hash[MOVER_HASH_INDEX] == "wtm"):
            hash[MOVER_HASH_INDEX] = "btm"
        else:
            hash[MOVER_HASH_INDEX] = "wtm"

        current = self.half_move_counter_list[-1]
        self.half_move_counter_list.append(current + 1)

        hash[HALF_MOVE_HASH_INDEX] = current + 1
        hash[FULL_MOVE_HASH_INDEX] += 0.5

        # any pawn move or capture should reset the 50 move rule counter
        if (from_piece.upper() == 'P' or piece_name.has_key(to_square)):
            hash[HALF_MOVE_HASH_INDEX] = 0
            self.half_move_counter_list[-1] = 0

        # check if there is a captured piece
        # this is subtle: there is no pawn on the to_square
        # for an enpassant capture.  That is handled later.
        if (piece_name.has_key(to_square)):
            to_piece = piece_name[to_square]
            # remove the captured piece from BB
            piece_bb[to_piece] = piece_bb[to_piece] & ~to_square
            piece_count[to_piece] -= 1
            # for captured rooks, we need to remove the castling
            # information so we don't get confused later.
            # We negate the location so we know it is a captured
            # rook.
            if (to_piece == "R"):
                if (self.w_rook_a1_location == to_square):
                    self.w_rook_a1_location = -to_square
                elif (self.w_rook_h1_location == to_square):
                    self.w_rook_h1_location = -to_square
                else:
                    print "Error: make_move white rook at invalid location"

            elif (to_piece == "r"):
                if (self.b_rook_a8_location == to_square):
                    self.b_rook_a8_location = -to_square
                elif (self.b_rook_h8_location == to_square):
                    self.b_rook_h8_location = -to_square
                else:
                    print "Error: make_move black rook at invalid location"

        # move the piece to new square on board
        piece_name[to_square] = piece_name[from_square]

        del piece_name[from_square]
        hash[bin2index[from_square]] = '-'
        # clear the from square from the position from_piece BB
        piece_bb[from_piece] = piece_bb[from_piece] & ~from_square 
        # add the piece in its new position
        piece_bb[from_piece] = piece_bb[from_piece] | to_square
        hash[bin2index[to_square]] = from_piece

        ########## handle special moves #########
        # for castling, move the associated rook
        if (move_name == "castle"):
            if (to_square == g1):
                from_rook = h1
                to_rook = f1
                rook = "R"
                self.w_rook_h1_move_count += 1
                self.w_rook_h1_location = f1
            elif (to_square == c1):
                from_rook = a1
                to_rook = d1
                rook = "R"
                self.w_rook_a1_move_count += 1
                self.w_rook_a1_location = d1
            elif (to_square == g8):
                from_rook = h8
                to_rook = f8
                rook = "r"
                self.b_rook_h8_move_count += 1
                self.b_rook_h8_location = f8
            elif (to_square == c8):
                from_rook = a8
                to_rook = d8
                rook = "r"
                self.b_rook_a8_move_count += 1
                self.b_rook_a8_location = d8
            else:
                print "Error: Invalid castle move %s-%s" % move

            # remove old rook
            piece_bb[rook] = piece_bb[rook] & ~from_rook
            del piece_name[from_rook]
            hash[bin2index[from_rook]] = '-'
            # add in new rook position
            piece_bb[rook] = piece_bb[rook] | to_rook
            piece_name[to_rook] = rook
            hash[bin2index[to_rook]] = rook

        # for en passant
        elif (move_name == "enpassant"):
            new_rank = rank[to_square]
            if (new_rank == 6): 
                # we're dealing with white capturing black
                removed_pawn_square = to_square >> 8 
                pawn = "p"
            elif (new_rank == 3):
                # we're dealing with black capturing white
                removed_pawn_square = to_square << 8 
                pawn = "P"
            else:
                print "Error: Invalid en passant move %s-%s" % move
            # remove captured pawn
            piece_bb[pawn] = piece_bb[pawn] & ~removed_pawn_square
            del piece_name[removed_pawn_square]
            hash[bin2index[removed_pawn_square]] = '-'
            piece_count[pawn] -= 1

        # pawn promotions
        elif (move_name == "promotion"):
            if (not promoted_piece):
                promoted_piece = "Q"
            if (from_piece == "P"):
                pawn = "P"
                new_promoted_piece = promoted_piece
                from_piece = new_promoted_piece
            else:
                pawn = "p"
                new_promoted_piece = promoted_piece.lower()
                from_piece = new_promoted_piece
            # remove the pawn
            piece_bb[pawn] = piece_bb[pawn] & ~to_square
            piece_count[pawn] -= 1
            # add a new_promoted_piece
            piece_bb[new_promoted_piece] = piece_bb[new_promoted_piece] | to_square
            piece_name[to_square] = new_promoted_piece
            piece_count[new_promoted_piece] += 1
            hash[bin2index[to_square]] = new_promoted_piece

        # make sure we can prevent castling in the future
        # this is just for rook moves since castling is handled above
        # handle the location update
        if (from_piece == 'R'):
            if (self.w_rook_a1_location == from_square):
                self.w_rook_a1_location = to_square
                self.w_rook_a1_move_count += 1
            elif (self.w_rook_h1_location == from_square):
                self.w_rook_h1_location = to_square
                self.w_rook_h1_move_count += 1              
        elif (from_piece == 'r'):
            if (self.b_rook_a8_location == from_square):
                self.b_rook_a8_location = to_square
                self.b_rook_a8_move_count += 1
            elif (self.b_rook_h8_location == from_square):
                self.b_rook_h8_location = to_square
                self.b_rook_h8_move_count += 1

        if (from_piece == 'K'): 
            self.w_king_move_count += 1
        elif (from_piece == 'k'): 
            self.b_king_move_count += 1

        self.w_pawn_last_double_move = 0
        self.b_pawn_last_double_move = 0

        hash[ENPASSANT_HASH_INDEX] = '-'
        if (move_name == "pawn double move"):
            if (from_piece == "P"):
                self.w_pawn_last_double_move = to_square
                hash[ENPASSANT_HASH_INDEX] = bin2alg[to_square>>8]
            else:
                self.b_pawn_last_double_move = to_square
                hash[ENPASSANT_HASH_INDEX] = bin2alg[to_square<<8]

        hash[CASTLING_HASH_INDEX] = '-'
        if (self.w_king_move_count == 0 and
            self.w_rook_h1_move_count == 0):
            hash[CASTLING_HASH_INDEX] = "%s%s" % (hash[CASTLING_HASH_INDEX],"K")
        if (self.w_king_move_count == 0 and
            self.w_rook_a1_move_count == 0):
            hash[CASTLING_HASH_INDEX] = "%s%s" % (hash[CASTLING_HASH_INDEX],"Q")
        if (self.b_king_move_count == 0 and
            self.b_rook_h8_move_count == 0):
            hash[CASTLING_HASH_INDEX] = "%s%s" % (hash[CASTLING_HASH_INDEX],"k")
        if (self.b_king_move_count == 0 and
            self.b_rook_a8_move_count == 0):
            hash[CASTLING_HASH_INDEX] = "%s%s" % (hash[CASTLING_HASH_INDEX],"q")
        if (len(hash[CASTLING_HASH_INDEX]) > 1):
            hash[CASTLING_HASH_INDEX] = hash[CASTLING_HASH_INDEX][1:]

        piece_bb['w_occupied'] = piece_bb['P']|piece_bb['R']|piece_bb['N']|\
                                 piece_bb['B']|piece_bb['Q']|piece_bb['K']
        piece_bb['b_occupied'] = piece_bb['p']|piece_bb['r']|piece_bb['n']|\
                                 piece_bb['b']|piece_bb['q']|piece_bb['k']

        # the hash should have been completed by now so we can save
        # this information for the repitition checks.
        # any pawn moves or captures reset the repetition check
        if (hash[HALF_MOVE_HASH_INDEX] == 0):
            self.position_counter_array_list.append({})
        else:
            hash_index = str(self.hash_index[0:64])
            # get the current array...it's last in the list
            current_array = dict(self.position_counter_array_list[-1])
            if (current_array.has_key(hash_index)):
                current_array[hash_index] += 1
            else:
                current_array[hash_index] = 1

            self.position_counter_array_list.append(dict(current_array))

        # We don't update the attacks_from and attacks_to after
        # each move since this seems more expensive then doing
        # it before we generate moves.
        return

    def unmake_move (self,move):
        from_square = move.from_square
        to_square = move.to_square
        move_name = move.move_name
        captured_piece = move.captured_piece
        promoted_piece = move.promoted_piece
        piece_name = self.piece_name
        piece_bb = self.piece_bb
        piece_count = self.piece_count
        to_piece = piece_name[to_square] 
        hash = self.hash_index

        if (DEBUG_MOVES):
            print "unmake_move =",move

        if (hash[MOVER_HASH_INDEX] == "wtm"):
            hash[MOVER_HASH_INDEX] = "btm"
        else:
            hash[MOVER_HASH_INDEX] = "wtm"

        hash[FULL_MOVE_HASH_INDEX] -= 0.5
        # any move we unmake simply gets rid of the
        # last value in the list and resets the current value

        # get rid of the last entry in half move list for repetition check
        self.position_counter_array_list.pop()        
        self.half_move_counter_list.pop()
        last_value = self.half_move_counter_list[-1]
        hash[HALF_MOVE_HASH_INDEX] = last_value

        # make sure we can prevent castling in the future
        if (to_piece == 'K'):
            self.w_king_move_count -= 1
        elif (to_piece == 'k'):
            self.b_king_move_count -= 1
        elif (to_piece == 'R'):
            if (self.w_rook_a1_location == to_square):
                self.w_rook_a1_move_count -= 1
                self.w_rook_a1_location = from_square
            elif (self.w_rook_h1_location == to_square):
                self.w_rook_h1_move_count -= 1              
                self.w_rook_h1_location = from_square
        elif (to_piece == 'r'):
            if (self.b_rook_a8_location == to_square):
                self.b_rook_a8_move_count -= 1
                self.b_rook_a8_location = from_square
            elif (self.b_rook_h8_location == to_square):
                self.b_rook_h8_move_count -= 1              
                self.b_rook_h8_location = from_square

        self.w_pawn_last_double_move = 0
        self.b_pawn_last_double_move = 0

        # move the piece back to the old square on board
        piece_name[from_square] = piece_name[to_square]
        hash[bin2index[from_square]] = to_piece
        hash[bin2index[to_square]] = '-'
        del piece_name[to_square]
        # clear the to square from the position to_piece BB
        piece_bb[to_piece] = piece_bb[to_piece] & ~to_square 
        # add the piece in its old position
        piece_bb[to_piece] = piece_bb[to_piece] | from_square

        ########## handle special moves #########
        # for castling move the associated rook back
        if (move_name == "castle"):
            if (to_square == g1):
                from_rook = f1
                to_rook = h1
                rook = "R"
                self.w_rook_h1_move_count -= 1
                self.w_rook_h1_location = h1
            elif (to_square == c1):
                from_rook = d1
                to_rook = a1
                rook = "R"
                self.w_rook_a1_move_count -= 1
                self.w_rook_a1_location = a1
            elif (to_square == g8):
                from_rook = f8
                to_rook = h8
                rook = "r"
                self.b_rook_h8_move_count -= 1
                self.b_rook_h8_location = h8
            elif (to_square == c8):
                from_rook = d8
                to_rook = a8
                rook = "r"
                self.b_rook_a8_move_count -= 1
                self.b_rook_a8_location = a8
            else:
                print "Error: Invalid castle move %s-%s" % move
            # remove old rook
            piece_bb[rook] = piece_bb[rook] & ~from_rook
            del piece_name[from_rook]
            hash[bin2index[from_rook]] = '-'
            # add in new rook position
            piece_bb[rook] = piece_bb[rook] | to_rook
            piece_name[to_rook] = rook
            hash[bin2index[to_rook]] = rook

        # for en passant add the captured pawn back to board
        elif (move_name == "enpassant"):
            new_rank = rank[from_square]
            # if we are unmaking an en passant move, that means the
            # last move was a pawn double move...so we need to make sure
            # that the flag is restored.
            if (new_rank == 5): 
                # we're dealing with white capturing black
                removed_pawn_square = to_square >> 8 
                self.b_pawn_last_double_move = removed_pawn_square
                pawn = "p"
            elif (new_rank == 4):
                # we're dealing with black capturing white
                removed_pawn_square = to_square << 8 
                self.w_pawn_last_double_move = removed_pawn_square
                pawn = "P"
            else:
                print "Error: Invalid en passant move %s-%s" % move
            # add back captured pawn
            piece_bb[pawn] = piece_bb[pawn] | removed_pawn_square
            piece_name[removed_pawn_square] = pawn
            hash[bin2index[removed_pawn_square]] = pawn
            piece_count[pawn] += 1

        # pawn promotions
        elif (move_name == "promotion"):
            # we're dealing with white
            if (not promoted_piece):
                promoted_piece = "Q"

            if (to_piece == to_piece.upper()):
                pawn = "P"
                new_promoted_piece = promoted_piece.upper()
                to_piece = "P"
            else:
                pawn = "p"
                new_promoted_piece = promoted_piece.lower()
                to_piece = "p"

            # add the pawn back
            piece_bb[pawn] = piece_bb[pawn] | from_square
            piece_name[from_square] = pawn
            hash[bin2index[from_square]] = pawn
            piece_count[pawn] += 1
            # remove a new_promoted_piece
            # we moved the new_promoted_piece back above so we need to remove it
            piece_bb[new_promoted_piece] = piece_bb[new_promoted_piece] & ~from_square
            piece_count[new_promoted_piece] -= 1
            if (captured_piece):
                # add the captured piece back to BB
                piece_bb[captured_piece] = piece_bb[captured_piece] | to_square
                piece_count[captured_piece] += 1
                piece_name[to_square] = captured_piece
                hash[bin2index[to_square]] = captured_piece
                if (captured_piece == "R"):
                    if (self.w_rook_a1_location == -to_square):
                        self.w_rook_a1_location = to_square                
                    elif (self.w_rook_h1_location == -to_square):
                        self.w_rook_h1_location = to_square
                elif (captured_piece == "r"):
                    if (self.b_rook_a8_location == -to_square):
                        self.b_rook_a8_location = to_square
                    elif (self.b_rook_h8_location == -to_square):
                        self.b_rook_h8_location = to_square
        # check if there was a captured piece
        # subtle item: if there was an enpassant capture,
        # there is no pawn on the to_square.  Putting the captured
        # pawn back is handled above so this needs to be an elif.
        elif (captured_piece):
            # add the captured piece back to BB
            piece_bb[captured_piece] = piece_bb[captured_piece] | to_square
            piece_name[to_square] = captured_piece
            hash[bin2index[to_square]] = captured_piece
            piece_count[captured_piece] += 1
            # for captured rooks, we need to add the castling
            # information so we don't get confused later
            if (captured_piece == "R"):
                if (self.w_rook_a1_location == -to_square):
                    self.w_rook_a1_location = to_square                
                elif (self.w_rook_h1_location == -to_square):
                    self.w_rook_h1_location = to_square
            elif (captured_piece == "r"):
                if (self.b_rook_a8_location == -to_square):
                    self.b_rook_a8_location = to_square
                elif (self.b_rook_h8_location == -to_square):
                    self.b_rook_h8_location = to_square

        piece_bb['w_occupied'] = piece_bb['P']|piece_bb['R']|piece_bb['N']|\
                                 piece_bb['B']|piece_bb['Q']|piece_bb['K']
        piece_bb['b_occupied'] = piece_bb['p']|piece_bb['r']|piece_bb['n']|\
                                 piece_bb['b']|piece_bb['q']|piece_bb['k']

        # We don't calculate attacks_to and attacks_from here
        # since it seems more expensive then doing all at once
        # before we generate moves
        return

    def order_moves(self,old_moves,wtm):
        """
        We step through the possible moves and assign a score to
        each move based on the number of opponent pieces it attacks
        and the number of pieces it defends. We pick only the top
        few moves.  We also consider whether we are attacked.
        """
        print "order_moves: starting"
        if (wtm):
            other_pieces = 'b_occupied'
            our_pieces = 'w_occupied'
        else:
            other_pieces = 'w_occupied'
            our_pieces = 'b_occupied'

        temp_moves = []
        for m in old_moves:
            value = 0
            #print "move is", m
            self.make_move(m)
            first_moves = self.generate_moves(wtm)
            for first_m in first_moves:
                if (m.to_square == first_m.from_square):
                    self.make_move(first_m)
                    second_moves = self.generate_moves(wtm)
                    for second_m in second_moves:
                        if (first_m.to_square == second_m.from_square):
                            self.make_move(second_m)
                            third_moves = self.generate_moves(wtm)
                            for third_m in third_moves:
                                if (second_m.to_square == third_m.from_square):
                                    # are we attacking the opponent's piece?
                                    if (third_m.to_square & self.piece_bb[other_pieces]):
                                        value += nipc(third_m.to_square & self.piece_bb[other_pieces])
                                    # are we protecting our own?
                                    if (self.attacks_from[third_m.from_square] & \
                                          self.piece_bb[our_pieces]):
                                        # this can have more then one value since we
                                        # could protect multiple pieces
                                        value += nipc(self.attacks_from[third_m.from_square] & \
                                                      self.piece_bb[our_pieces])                
                                    # are we being attacked by the opponent?
                                    if (self.attacks_to[third_m.from_square] & \
                                          self.piece_bb[other_pieces]):
                                        # this can have more then one value since we
                                        # could protect multiple pieces
                                        value += nipc(self.attacks_to[third_m.from_square] & \
                                                      self.piece_bb[other_pieces])                

                            self.unmake_move(second_m)

                    self.unmake_move(first_m)

            self.unmake_move(m)

            bisect.insort(temp_moves,(value,m))

        temp_moves.reverse()
        moves = []
        for i in temp_moves:
            moves.append(i[1])

        return(moves) # only the first 5 moves? [0:5])

    def eval (self,wtm,depth=0):
        """
        This is the main evaluation functions.  It looks at the
        following things:
        1. Material score
        2. pawn evaluation
        3. piece placement
        4. piece mobility
        """
        value = 0

        piece_bb = self.piece_bb
        count = self.piece_count

        black_pieces = piece_bb['b_occupied']
        white_pieces = piece_bb['w_occupied']
        all_pieces = piece_bb['b_occupied'] | piece_bb['w_occupied']

        # 1. Material score
        value += KING_VALUE   * (count["K"] - count["k"]) + \
                 QUEEN_VALUE  * (count["Q"] - count["q"]) + \
                 ROOK_VALUE   * (count["R"] - count["r"]) + \
                 BISHOP_VALUE * (count["B"] - count["b"]) + \
                 KNIGHT_VALUE * (count["N"] - count["n"]) + \
                 PAWN_VALUE   * (count["P"] - count["p"]) 

        """
        # 2a. evaluate white passed pawns first

        wp = piece_bb['P']
        bp = piece_bb['p']
        white_passed_pawns = 0
        while (wp):
            pawn = ((wp) & -(wp))
            # add in pawn piece square since it saves cycles to do it here
            value += piece_square_value["P"][pawn]
            # a passed pawn has no opponent pawns in front of it and
            # on either file.
            if ((file_mask[pawn] & bp == 0) and \
                (file_mask[pawn<<1] & bp & ~file_mask[h1] & above[pawn] == 0) and \
                (file_mask[pawn>>1] & bp & ~file_mask[a1] & above[pawn] == 0)):
                value += PASSED_PAWN_MULT * rank[pawn]
                white_passed_pawns |= pawn
                # if the king supports the pawn, it is even more valuable
                if (king_moves[piece_bb['K']] & pawn != 0):
                    value += PASSED_PAWN_KING_SUPPORTED_MULT * rank[pawn]
            # if there is no opponent piece blocking it, it is worth more.
            if (file_mask[pawn] & black_pieces & above[pawn] == 0):
                value += PASSED_PAWN_UNBLOCKED_MULT * rank[pawn]
            wp = ((wp) & ((wp) - 1L))

        # 2b. evaluate black passed pawns 
        wp = piece_bb['P']
        bp = piece_bb['p']
        black_passed_pawns = 0
        while (bp):
            pawn = ((bp) & -(bp))
            # add in pawn piece square since it saves cycles to do it here
            value -= piece_square_value["p"][pawn]
            # a passed pawn has no opponent pawns in front of it and
            # on either file.
            if ((file_mask[pawn] & wp == 0) and \
                (file_mask[pawn<<1] & wp & ~file_mask[h1] & below[pawn] == 0) and \
                (file_mask[pawn>>1] & wp & ~file_mask[a1] & below[pawn] == 0)):
                value -= PASSED_PAWN_MULT * (8 - rank[pawn])
                black_passed_pawns |= pawn
                # if the king supports the pawn, it is even more valuable
                if (king_moves[piece_bb['k']] & pawn != 0):
                    value -= PASSED_PAWN_KING_SUPPORTED_MULT * (8 - rank[pawn])

            # if there is no opponent piece blocking it, it is worth more.
            if (file_mask[pawn] & white_pieces & below[pawn] == 0):
                value -= PASSED_PAWN_UNBLOCKED_MULT * (8 - rank[pawn])
            bp = ((bp) & ((bp) - 1L))

        # 3. Piece Position add in the rest of the piece square values
        #    for the rest of the pieces
        multiplier = 1
        for name in "NnBbRrQqKk":
            bb = piece_bb[name]
            while (bb):
                loc = ((bb) & -(bb))
                value += multiplier * piece_square_value[name][loc]
                bb = ((bb) & ((bb) - 1L))

            # since we need to subtract the black values, invert multiplier
            multiplier *= -1
        """

        """
        # 4. Piece Mobility: Give extra points for greater number of moves
        #    from a particular position.
        #    We don't need to worry about pinned pieces for now.
        w_pieces = piece_bb['K'] | piece_bb['Q'] | piece_bb['R'] | \
                   piece_bb['B'] | piece_bb['N'] 
        b_pieces = piece_bb['k'] | piece_bb['q'] | piece_bb['r'] | \
                   piece_bb['b'] | piece_bb['n'] 
        kings = piece_bb['k'] | piece_bb['K']
        knights = piece_bb['n'] | piece_bb['N']
        queen_rooks = piece_bb['Q'] | piece_bb['q'] | piece_bb['R'] | piece_bb['r']
        queen_bishops = piece_bb['Q'] | piece_bb['q'] | piece_bb['B'] | piece_bb['b']
        multiplier = 1
        self.generate_attacks()
        for (pieces,our_pieces,other_pieces) in \
            (w_pieces,white_pieces,black_pieces),(b_pieces,black_pieces,white_pieces):
            moves = 0
            while (pieces):
                from_square = ((pieces) & -(pieces))
                # 5. Piece Strength: Give extra points for pieces that attack
                #    opponent pieces or protect our pieces.  Also deduct points
                #    if the piece is attacked by opponent pieces.
                # are we attacking opponent pieces
                if (self.attacks_from[from_square] & other_pieces):
                    value += ATTACKING_VALUE * multiplier * \
                             nipc(self.attacks_from[from_square] & other_pieces)
                # are we protecting our pieces
                if (self.attacks_from[from_square] & our_pieces):
                    value += PROTECTING_VALUE * multiplier * \
                             nipc(self.attacks_from[from_square] & our_pieces)
                # are we being attacked by opponent pieces
                if (self.attacks_to[from_square] & other_pieces):
                    value += -1 * ATTACKED_VALUE * multiplier * \
                             nipc(self.attacks_to[from_square] & other_pieces)
                    
                rank_pieces = rank_mask[from_square & queen_rooks] & all_pieces
                file_pieces = file_mask[from_square & queen_rooks] & all_pieces
                ne_pieces = diag_mask_ne[from_square & queen_bishops] & all_pieces
                nw_pieces = diag_mask_nw[from_square & queen_bishops] & all_pieces
                moves |= ((king_moves[from_square & kings] & other_pieces)        | \
                          (king_moves[from_square & kings] & ~all_pieces)         | \
                          (knight_moves[from_square & knights] & other_pieces)    | \
                          (knight_moves[from_square & knights] & ~all_pieces)     | \
                          (rank_attacks[from_square & queen_rooks][rank_pieces] & other_pieces) | \
                          (rank_attacks[from_square & queen_rooks][rank_pieces] & ~all_pieces)  | \
                          (file_attacks[from_square & queen_rooks][file_pieces] & other_pieces) | \
                          (file_attacks[from_square & queen_rooks][file_pieces] & ~all_pieces)  | \
                          (diag_attacks_ne[from_square & queen_bishops][ne_pieces] & other_pieces) | \
                          (diag_attacks_ne[from_square & queen_bishops][ne_pieces] & ~all_pieces)  | \
                          (diag_attacks_nw[from_square & queen_bishops][nw_pieces] & other_pieces) | \
                          (diag_attacks_nw[from_square & queen_bishops][nw_pieces] & ~all_pieces))
                pieces = ((pieces) & ((pieces) - 1L))

            value += MOBILITY_VALUE * multiplier * nipc(moves)
            multiplier *= -1
        """

        # 6. Give extra points when the king stays on the same square as
        #    the bishops.

        # if a repetition is detected, we need to adjust the evaluation 
        #hash_index = str(self.hash_index[:64])
        #current_array = self.position_counter_array_list[-1]
        #if (current_array.has_key(hash_index) and \
        #    current_array[hash_index] >= 2):
        #    print "Repetition check",current_array[hash_index]
        #    if (wtm):
        #        value -= 100000
        #    else:
        #        value += 100000

        # need to negate the value for black moves since
        # negamax expects this.
        if (wtm == 0):
            value = -value

        return(value)
    
def ipc (b=0):
    '''
    iterative population count
    '''
    n = 0
    while b != 0:
        n = n + 1
        b = b & (b - 1)
    return n;

def nipc (b=0):
    '''
    non iterative pop count
    '''
    m1 = 0x5555555555555555
    m2 = 0x3333333333333333
    n = 0
    a = b - ((b >> 1) & m1)
    c = (a & m2) + ((a >> 2) & m2)
    n = (c + (c >> 32))
    n = (n & 0x0F0F0F0F) + ((n >> 4) & 0x0F0F0F0F)
    n = (n & 0xFFFF) + (n >> 16)
    n = (n & 0xFF) + (n >> 8)
    return n

def lsb (b):
    """
    Least Significant Bit.
    We simply return b & -b or we can return  b & ~(b - 1)
    which takes a little more time.
    """
    return(b & -b)

def clear_lsb (b):
    """
    Clear the ( and return the number. & - and return the number.)
    """
    return(b & (b-1L))

def msb (b=0):
    """
    Most Significant Bit.  This isn't used.
    This is faster then msb2 for small numbers of 1 bits
    """
    while b != 0:
        msb = b
        b = ((b) & ((b) - 1L))
    return(msb)

def lsb2 (b):
    """
    Yet another way of calculating LSB.  This is slower then lsb().
    lsb = msb(b XOR (b-1)))
    """
    return(msb(b ^ (b-1L)))

def msb2 (b=0):
    """
    This isn't used.  This is just another way to
    calculate the MSB.  This is faster then msb for large numbers of 1 bits
    """
    log2=0.69314718055994529
    return(2**int((math.log(b)/log2)))

def frombase (number,b):
    # converts the given string to an
    # arbitrary base.  Result is a number base 10
    # '11' base to base 256 = 257 (base10)
    result = 0
    l = list(number)
    l.reverse()
    for i in range(len(l)):
        result += int(l[i]) * (b**i)
    return(result)

def tobase (n,b,result=''):
    # this converts a number that is in base 10 to another base
    # i.e. tobase(16,16) = '10'
    if n == 0:
        if result:
            return result
        else:
            return '0'
    else:
        return tobase(n/b,b,str(n%b)+result)
    return

def rank_to_file (n):
    # return the row to file conversion for the first rank
    return(frombase(str(tobase(n,2)),256))

def rd128 (n):
    # return the row to file conversion for the first rank
    return(frombase(str(tobase(n,2)),128))

def rd512 (n):
    # return the row to file conversion for the first rank
    return(frombase(str(tobase(n,2)),512))

def display (x=None):
    if (type(x) == types.DictType):
        display_position(x)
    elif (type(x) == types.LongType or type(x) == types.IntType):
        display_bb(x)
    elif (type(x) == types.ListType):
        display_moves(x)

def display_position (position=None):
    if (not position):
        print "Error: display missing position"
        return
    piece_name = self.piece_name
    white = 1
    for r in range(8,0,-1):
        print "\n    +---+---+---+---+---+---+---+---+"
        print " ",r, "|",
        for f in "abcdefgh":
            name = "%s%s" % (f,r)
            bb = alg2bin[name]
            if (piece_name.has_key(bb)):
                print piece_name[bb],"|",
            else:
                if (white):
                    print " ","|",
                else:
                    print ".","|",
            white ^= 1
        white ^= 1
    print "\n    +---+---+---+---+---+---+---+---+"
    print "      a   b   c   d   e   f   g   h  \n"
    return

def display_bb (bb=None):
    if (bb == None):
        print "Error: display missing BitBoard"
        return
    white = 1
    for r in range(8,0,-1):
        print "\n    +---+---+---+---+---+---+---+---+"
        print " ",r, "|",
        for f in range(8,0,-1):
            val = (8L * (r - 1L)) + (f - 1L)
            if ((1<<val) & bb):
                print '1',"|",
            else:
                if (white):
                    print " ","|",
                else:
                    print ".","|",
            white ^= 1
        white ^= 1
    print "\n    +---+---+---+---+---+---+---+---+"
    print "      a   b   c   d   e   f   g   h  \n"
    return

def display_attacks (position=None):
    if (not position):
        print "Error: display missing position"
        return
    from_keys = position["attacks_from"].keys()
    for i in from_keys:
        attacks = position["attacks_from"][i]
        if (attacks):
            print "\nattacks from %s to " % (bin2alg[i]),
        while (attacks):
            to_square = ((attacks) & -(attacks))
            print "%s " % (bin2alg[to_square]),
            attacks = ((attacks) & ((attacks) - 1L))
            
    print
    to_keys = position["attacks_to"].keys()
    for i in to_keys:
        attacks = position["attacks_to"][i]
        if (attacks):
            print "\nattacks to %s from " % (bin2alg[i]),
        while (attacks):
            from_square = ((attacks) & -(attacks))
            print "%s " % (bin2alg[from_square]),
            attacks = ((attacks) & ((attacks) - 1L))
    print
    return

def pb (b):
    # print the bit board of the 64 bit number
    buff = ''
    for i in range(8):
        buff = '%08d\n%s' % (int(tobase((255 & (b>>(i*8))),2)),buff)
    print buff
    return

def mainloop2 ():
    """
    This main loop isn't used.  It may be used later to
    allow the computer to ponder moves while the opponent
    is thinking.
    """
    count = 0
    buff = ''
    data=None
    addr=None
    default = 2.0
    send_time = 0.0
    temp_count = 0
    stdin = sys.stdin
    gettime = time.time
    selector = select.select
    reader = stdin.readline
    readlist = [stdin]
    emptylist = []
    while 1:
        current = gettime()
        diff = current-send_time
        if diff > default:
            temp_count = count - temp_count
            message = 'keepalive diff=%s current=%16.6f count=%s' % \
                      (diff,current,temp_count)
            print message
            temp_count=count
            send_time = current
        count = count+1
        # check for keyboard input
        rl,wl,el = selector(readlist,emptylist,emptylist,0)
        for foo in rl:
            myline = reader()
            print "Got line", myline
    return

def get_position (board={}):
    position = zero_position()
    for i in range(64):
        bin = 1L<<i
        if (board.has_key(bin)):
            piece = board[bin]
            if (position.has_key(piece)):
                position[piece] |= bin
            else:
                position[piece] = bin
    return(position)

def get_board (position={}):
    board = {}
    for i in "PNBRQKpnbrqk":
        piece = position[i]
        while (piece):
            one_piece = ((piece) & -(piece))
            board[one_piece]=i
            piece = ((piece) & ((piece) - 1L))
    return(board)
   
def add_attacks (attacks_from,attacks_to,from_square,to_square):
    if (attacks_from[from_square]):
        attacks_from[from_square] |= to_square
    else:
        attacks_from[from_square] = to_square
    if (attacks_to[to_square]):
        attacks_to[to_square] |= from_square
    else:
        attacks_to[to_square] = from_square
    
def get_conversions ():
    """
    These arrays are just handy conversions that are used
    throughout the program.  "a1" = 128, etc.
    """
    bin2alg = {}
    bin2index = {}
    alg2bin = {}
    count = 0
    for i in range(1,9):
        for j in 'hgfedcba':
            name = '%s%s' % (j,i)
            bin2alg[1L<<count] = name     # bin2alg[1<<7] = 'a1'
            alg2bin[name] = 1L<<count
            bin2index[1L<<count] = count  # bin2index[a1] = 7
            count = count + 1
    bin2alg[0] = 0
    alg2bin[0] = 0
    return((bin2alg,bin2index,alg2bin))

def get_direction_masks ():
    above = {}
    below = {}
    left = {}
    right = {}
    white_squares = 0
    black_squares = 0
    for i in range(64):
        bb = 1L<<i
        if ((rank[bb] + file[bb]) % 2 == 0):
            black_squares |= bb
        else:
            white_squares |= bb

        below[bb] = ALL_ONES & ~rank_mask[bb]
        r = rank[bb]
        for a in range(r+1, 9):
            below[bb] &= ~rank_mask[bb<<(8*(9-a))]

        above[bb] = ~below[bb] & ~rank_mask[bb]

        left[bb] = ALL_ONES & ~file_mask[bb]
        f = file[bb]
        for a in range(f+1,9):
            left[bb] &=  ~file_mask[bb>>(9-a)]

        right[bb] = ~left[bb] & ~file_mask[bb]

    return(above,below,left,right,white_squares,black_squares)

def get_files ():
    file8 = 1L<<0 | 1L<<8 | 1L<<16 | 1L<<24 | 1L<<32 | 1L<<40 | 1L<<48 | 1L<<56
    file = {}
    file_mask = {}
    count = 0
    file_mask[0] = 0
    file[0] = 0
    for i in range(1,9):
        for j in range(8,0,-1):
            file[1L<<count]      = j
            file_mask[1L<<count] = file8<<(8-j)
            count = count + 1
    return(file,file_mask)

def get_ranks ():
    rank = {}
    rank_mask = {}
    count = 0
    rank[0] = 0
    rank_mask[0] = 0
    for i in range(1,9):
        for j in range(8,0,-1):
            rank[1L<<count]      = i
            rank_mask[1L<<count] = (255L<<8*(i-1))
            count = count + 1
    return(rank,rank_mask)

def get_attacks (square_list=None):
    # This routine is called at startup to fill the
    # attack hash table for direct lookup.
    # square_list is a list of lists containing
    # the squares we will move over to find the attacks.
    attack_table = {}
    attack_table[0] = {}
    attack_table[0][0] = 0
    # loop over the list of square lists (first index)
    for i in range(len(square_list)):
        list_size = len(square_list[i])
        # loop over this particular list of squares (second index)
        for current_position in range(list_size):
            current_bb = square_list[i][current_position]
            attack_table[current_bb] = {}
            # now loop over an occupation number
            for occupation in range(1L<<list_size):
                moves = 0
                # loop over the squares to the right of the mover
                for newsquare in range(current_position+1,list_size):
                    moves |= square_list[i][newsquare]
                    # we've found a blocking piece, bail out.
                    if ((1L<<newsquare) & occupation):
                        break
                # loop over the squares to the left of the mover
                for newsquare in range(current_position-1,-1,-1):
                    moves |= square_list[i][newsquare]
                    # blocking piece found, bail out.
                    if ((1L<<newsquare) & occupation):
                        break
                # convert occupation to a bb number
                temp_bb = 0
                while (occupation):
                    lowest = ((occupation) & -(occupation))
                    temp_bb |= square_list[i][bin2index[lowest]] 
                    occupation = ((occupation) & ((occupation) - 1L))
                # record the possible attack moves for the
                # current bitboard square with the given occupation
                attack_table[current_bb][temp_bb] = moves

    return(attack_table)

def get_diag_attacks_ne ():
    # these are the diagonals but ordered from right to left.
    diag_values = [[h1],
                 [h2,g1],
                [h3,g2,f1],
               [h4,g3,f2,e1],
              [h5,g4,f3,e2,d1],
             [h6,g5,f4,e3,d2,c1],
            [h7,g6,f5,e4,d3,c2,b1],
           [h8,g7,f6,e5,d4,c3,b2,a1],
            [g8,f7,e6,d5,c4,b3,a2],
             [f8,e7,d6,c5,b4,a3],
              [e8,d7,c6,b5,a4],
               [d8,c7,b6,a5],
                [c8,b7,a6],
                 [b8,a7],
                  [a8]]
    return(get_attacks(diag_values))

def get_diag_attacks_nw ():
    # these are the diagonals but ordered from right to left
    diag_values = [[a1],
                 [b1,a2],
                [c1,b2,a3],
               [d1,c2,b3,a4],
              [e1,d2,c3,b4,a5],
             [f1,e2,d3,c4,b5,a6],
            [g1,f2,e3,d4,c5,b6,a7],
           [h1,g2,f3,e4,d5,c6,b7,a8],
            [h2,g3,f4,e5,d6,c7,b8],
             [h3,g4,f5,e6,d7,c8],
              [h4,g5,f6,e7,d8],
               [h5,g6,f7,e8],
                [h6,g7,f8],
                 [h7,g8],
                  [h8]]
    return(get_attacks(diag_values))

def get_file_attacks ():
    # these are the file square values
    file_values = [[a1,a2,a3,a4,a5,a6,a7,a8],
                   [b1,b2,b3,b4,b5,b6,b7,b8],
                   [c1,c2,c3,c4,c5,c6,c7,c8],
                   [d1,d2,d3,d4,d5,d6,d7,d8],
                   [e1,e2,e3,e4,e5,e6,e7,e8],
                   [f1,f2,f3,f4,f5,f6,f7,f8],
                   [g1,g2,g3,g4,g5,g6,g7,g8],
                   [h1,h2,h3,h4,h5,h6,h7,h8]]
    return(get_attacks(file_values))

def get_rank_attacks ():
    # these are the rank square values
    rank_values = [[a1,b1,c1,d1,e1,f1,g1,h1],
                   [a2,b2,c2,d2,e2,f2,g2,h2],
                   [a3,b3,c3,d3,e3,f3,g3,h3],
                   [a4,b4,c4,d4,e4,f4,g4,h4],
                   [a5,b5,c5,d5,e5,f5,g5,h5],
                   [a6,b6,c6,d6,e6,f6,g6,h6],
                   [a7,b7,c7,d7,e7,f7,g7,h7],
                   [a8,b8,c8,d8,e8,f8,g8,h8]]
    return(get_attacks(rank_values))

def get_rot90():
    # this hash table is used to keep track of a rotated occupation
    # bitboard that will only be used for testing.
    rot90 = {a1:a8, a2:b8, a3:c8, a4:d8, a5:e8, a6:f8, a7:g8, a8:h8,
             b1:a7, b2:b7, b3:c7, b4:d7, b5:e7, b6:f7, b7:g7, b8:h7,
             c1:a6, c2:b6, c3:c6, c4:d6, c5:e6, c6:f6, c7:g6, c8:h6,
             d1:a5, d2:b5, d3:c5, d4:d5, d5:e5, d6:f5, d7:g5, d8:h5,
             e1:a4, e2:b4, e3:c4, e4:d4, e5:e4, e6:f4, e7:g4, e8:h4,
             f1:a3, f2:b3, f3:c3, f4:d3, f5:e3, f6:f3, f7:g3, f8:h3,
             g1:a2, g2:b2, g3:c2, g4:d2, g5:e2, g6:f2, g7:g2, g8:h2,
             h1:a1, h2:b1, h3:c1, h4:d1, h5:e1, h6:f1, h7:g1, h8:h1}

    rotminus90 = {}
    for i in rot90.keys():
        rotminus90[rot90[i]] = i

    return(rot90,rotminus90)

def get_RankAttacks():
    # this hash table will return the rank attacks
    # for a given square and occupancy
    RankAttacks = {}
    for i in range(64):
        square = 1 << i
        RankAttacks[square] = {}
        shift = 8 * (rank[square] - 1)
        for occupancy in range(256):
            attacks = rank_attacks[square >> shift][occupancy]
            RankAttacks[square][occupancy] = attacks<<shift

    return(RankAttacks)
    
def get_FileAttacks():
    # this hash table will return the file attacks
    # for a given square and file occupancy
    # this is called with the bb square and the occupancy
    # rotated 90 degrees and shifted down...
    # but it has to give the file attacks
    # i.e. square = b3, occupancy = b1 | b6 | b7 | b8
    #     rotated90 c7              a7   f7   g7   h7
    #     shifted   c1              a1   f1   g1   h1 
    #     attacks  rank_attacks[c1][a1|f1|g1|h1]
    #   answer returned file_attacks[b3][b1 | b6 | b7 | b8]
    FileAttacks = {}
    for i in range(64):
        square = 1<<i
        square90 = rot90[1 << i]
        FileAttacks[square] = {}
        shift = 8 * (rank[square90] - 1)
        for occupancy in range(256):
            attacks = rank_attacks[square90 >> shift][occupancy]
            # takes attacks back up to the right rank
            attacks = attacks << shift
            # rotate the attacks back 90 degrees
            rotAttacks = 0
            while (attacks):
                lowest = lsb(attacks)
                rotAttacks |= rotminus90[lowest]
                attacks = clear_lsb(attacks)
                
            FileAttacks[square][occupancy] = rotAttacks

    return(FileAttacks)

def get_rot45ne():
    # this hash table is used to keep track of a rotated occupation
    # bitboard that will only be used for testing.
    rot45ne = {a1:a8, b2:b8, c3:c8, d4:d8, e5:e8, f6:f8, g7:g8, h8:h8,
               a8:a7, b1:b7, c2:c7, d3:d7, e4:e7, f5:f7, g6:g7, h7:h7,
               a7:a6, b8:b6, c1:c6, d2:d6, e3:e6, f4:f6, g5:g6, h6:h6,
               a6:a5, b7:b5, c8:c5, d1:d5, e2:e5, f3:f5, g4:g5, h5:h5,
               a5:a4, b6:b4, c7:c4, d8:d4, e1:e4, f2:f4, g3:g4, h4:h4,
               a4:a3, b5:b3, c6:c3, d7:d3, e8:e3, f1:f3, g2:g3, h3:h3, 
               a3:a2, b4:b2, c5:c2, d6:d2, e7:e2, f8:f2, g1:g2, h2:h2,
               a2:a1, b3:b1, c4:c1, d5:d1, e6:e1, f7:f1, g8:g1, h1:h1}

    rotminus45ne = {}
    for i in rot45ne.keys():
        rotminus45ne[rot45ne[i]] = i

    rot45ne_mask = {a1:0xff, b2:0xff, c3:0xff, d4:0xff, e5:0xff, f6:0xff, g7:0xff, h8:0xff,
                    a8:0x80, b1:0x7f, c2:0x7f, d3:0x7f, e4:0x7f, f5:0x7f, g6:0x7f, h7:0x7f,
                    a7:0xc0, b8:0xc0, c1:0x3f, d2:0x3f, e3:0x3f, f4:0x3f, g5:0x3f, h6:0x3f,
                    a6:0xe0, b7:0xe0, c8:0xe0, d1:0x1f, e2:0x1f, f3:0x1f, g4:0x1f, h5:0x1f,
                    a5:0xf0, b6:0xf0, c7:0xf0, d8:0xf0, e1:15,   f2:15,   g3:15,   h4:15,
                    a4:0xf8, b5:0xf8, c6:0xf8, d7:0xf8, e8:0xf8, f1:7,    g2:7,    h3:7, 
                    a3:0xfc, b4:0xfc, c5:0xfc, d6:0xfc, e7:0xfc, f8:0xfc, g1:3,    h2:3,
                    a2:0xfe, b3:0xfe, c4:0xfe, d5:0xfe, e6:0xfe, f7:0xfe, g8:0xfe, h1:1}
    return(rot45ne,rotminus45ne,rot45ne_mask)

def get_BishopAttacksNE():
    # this hash table will return the Diag NE attacks
    # for a given square and diag occupancy
    # this is called with the bb square and the occupancy
    # rotated 45 degrees and shifted down...
    # but it has to give the diag attacks
    BishopAttacksNE = {}
    for i in range(64):
        square = 1<<i
        square45ne = rot45ne[1 << i]
        BishopAttacksNE[square] = {}
        shift = 8 * (rank[square45ne] - 1)
        for occupancy in range(256):
            # we need to mask out the bits we don't want
            attacks = rank_attacks[square45ne >> shift][occupancy & rot45ne_mask[square]]
            # takes attacks back up to the right rank
            attacks = attacks << shift
            # rotate the attacks back 45 degrees
            rotAttacks = 0
            while (attacks):
                lowest = lsb(attacks)
                rotAttacks |= rotminus45ne[lowest]
                attacks = clear_lsb(attacks)
                
            BishopAttacksNE[square][occupancy] = rotAttacks

    return(BishopAttacksNE)

def get_rot45nw():
    # this hash table is used to keep track of a rotated occupation
    # bitboard that will only be used for testing.
    rot45nw = {a8:a8, b7:b8, c6:c8, d5:d8, e4:e8, f3:f8, g2:g8, h1:h8,
               a1:a7, b8:b7, c7:c7, d6:d7, e5:e7, f4:f7, g3:g7, h2:h7,
               a2:a6, b1:b6, c8:c6, d7:d6, e6:e6, f5:f6, g4:g6, h3:h6,
               a3:a5, b2:b5, c1:c5, d8:d5, e7:e5, f6:f5, g5:g5, h4:h5,
               a4:a4, b3:b4, c2:c4, d1:d4, e8:e4, f7:f4, g6:g4, h5:h4,
               a5:a3, b4:b3, c3:c3, d2:d3, e1:e3, f8:f3, g7:g3, h6:h3, 
               a6:a2, b5:b2, c4:c2, d3:d2, e2:e2, f1:f2, g8:g2, h7:h2,
               a7:a1, b6:b1, c5:c1, d4:d1, e3:e1, f2:f1, g1:g1, h8:h1}

    rotminus45nw = {}
    for i in rot45nw.keys():
        rotminus45nw[rot45nw[i]] = i

    rot45nw_mask = {a8:0xff, b7:0xff, c6:0xff, d5:0xff, e4:0xff, f3:0xff, g2:0xff, h1:0xff,
                    a1:0x80, b8:0x7f, c7:0x7f, d6:0x7f, e5:0x7f, f4:0x7f, g3:0x7f, h2:0x7f,
                    a2:0xc0, b1:0xc0, c8:0x3f, d7:0x3f, e6:0x3f, f5:0x3f, g4:0x3f, h3:0x3f,
                    a3:0xe0, b2:0xe0, c1:0xe0, d8:0x1f, e7:0x1f, f6:0x1f, g5:0x1f, h4:0x1f,
                    a4:0xf0, b3:0xf0, c2:0xf0, d1:0xf0, e8:15,   f7:15,   g6:15,   h5:15,
                    a5:0xf8, b4:0xf8, c3:0xf8, d2:0xf8, e1:0xf8, f8:7,    g7:7,    h6:7, 
                    a6:0xfc, b5:0xfc, c4:0xfc, d3:0xfc, e2:0xfc, f1:0xfc, g8:3,    h7:3,
                    a7:0xfe, b6:0xfe, c5:0xfe, d4:0xfe, e3:0xfe, f2:0xfe, g1:0xfe, h8:1}
    return(rot45nw,rotminus45nw,rot45nw_mask)

def get_BishopAttacksNW():
    # this hash table will return the Diag NW attacks
    # for a given square and diag occupancy
    # this is called with the bb square and the occupancy
    # rotated 45 degrees and shifted down...
    # but it has to give the diag attacks
    BishopAttacksNW = {}
    for i in range(64):
        square = 1<<i
        square45nw = rot45nw[1 << i]
        BishopAttacksNW[square] = {}
        shift = 8 * (rank[square45nw] - 1)
        for occupancy in range(256):
            # we need to mask out the bits we don't want
            attacks = rank_attacks[square45nw >> shift][occupancy & rot45nw_mask[square]]
            # takes attacks back up to the right rank
            attacks = attacks << shift
            # rotate the attacks back 45 degrees
            rotAttacks = 0
            while (attacks):
                lowest = lsb(attacks)
                rotAttacks |= rotminus45nw[lowest]
                attacks = clear_lsb(attacks)
                
            BishopAttacksNW[square][occupancy] = rotAttacks

    return(BishopAttacksNW)

def get_diag_ne ():
    # NE bottom half of the board
    diag_mask_ne = {}
    diag_mask_ne[0] = 0
    for i in range(8):
        diag_mask_ne[1L<<i] = 0
        for j in range(i+1):
            diag_mask_ne[1L<<i] |= (1L<<(i+7*j))
        for j in range(i+1):
            diag_mask_ne[1L<<(i+7*j)] = diag_mask_ne[1L<<i]
    # ne top half of the board
    for i in range(63,55,-1):
        diag_mask_ne[1L<<i] = 0
        for j in range(64-i):
            diag_mask_ne[1L<<i] |= (1L<<(i-7*j))
        for j in range(64-i):
            diag_mask_ne[1L<<(i-7*j)] = diag_mask_ne[1L<<i]
    return(diag_mask_ne)

def get_diag_nw ():
    # bottom half of the board
    diag_mask_nw = {}
    diag_mask_nw[0] = 0
    for i in range(7,-1,-1):
        diag_mask_nw[1L<<i] = 0
        for j in range(8-i):
            diag_mask_nw[1L<<i] |= (1L<<(i+9*j))
        for j in range(8-i):
            diag_mask_nw[1L<<(i+9*j)] = diag_mask_nw[1L<<i]
    # top half of the board
    for i in range(56,64):
        diag_mask_nw[1L<<i] = 0
        for j in range(i-55):
            diag_mask_nw[1L<<i] |= (1L<<(i-9*j))
        for j in range(i-55):
            diag_mask_nw[1L<<(i-9*j)] = diag_mask_nw[1L<<i]
    return(diag_mask_nw)

def get_knight_moves2 ():
    knight_moves = {}
    knight_moves[0] = 0
    for i in range(64):
        index = 1L<<i
        knight_moves[1L<<i] = 0
        if (((i+15) < 64) and (file[1L<<(i+15)] - file[index] == 1)):
            knight_moves[1L<<i] |= 1L<<(i+15)
        if (((i+6) < 64) and (file[1L<<(i+6)] - file[index] == 2)):
            knight_moves[1L<<i] |= 1L<<(i+6)
        if (((i+10) < 64) and (file[1L<<(i+10)] - file[index] == -2)):
            knight_moves[1L<<i] |= 1L<<(i+10)
        if (((i+17) < 64) and (file[1L<<(i+17)] - file[index] == -1)):
            knight_moves[1L<<i] |= 1L<<(i+17)
        if (((i-10) > -1) and (file[1L<<(i-10)] - file[index] == 2)):
            knight_moves[1L<<i] |= 1L<<(i-10)
        if (((i-17) > -1) and (file[1L<<(i-17)] - file[index] == 1)):
            knight_moves[1L<<i] |= 1L<<(i-17)
        if (((i-15) > -1) and (file[1L<<(i-15)] - file[index] == -1)):
            knight_moves[1L<<i] |= 1L<<(i-15)
        if (((i-6) > -1) and (file[1L<<(i-6)] - file[index] == -2)):
            knight_moves[1L<<i] |= 1L<<(i-6)
    return(knight_moves)

def get_knight_moves ():
    knight_moves = {}
    knight_moves[0] = 0
    # this is a typical knight attack number....for c6
    knight_attacks = a7|b8|d8|e7|e5|d4|b4|a5
    # we shift it back to a8 where we will start
    knight_attacks = knight_attacks << 18
    for i in range(64):
        square = 1L<<i
        # always shift down to the square we are working on
        ka = knight_attacks >> (63 - i)
        if (file[square] > 2 and file[square] < 7):
            knight_moves[square] = ka & ALL_ONES

        elif (file[square] < 3):
            knight_moves[square] = ka & ALL_ONES & \
                                   left[square>>3]

        elif (file[square] > 6):
            knight_moves[square] = ka & ALL_ONES & \
                                   right[square<<3]

    return(knight_moves)

def get_king_moves ():
    king_moves = {}
    king_moves[0] = 0
    for i in range(64):
        index = 1L<<i
        king_moves[1L<<i] = 0
        if (((i+1) < 64) and (file[1L<<(i+1)] - file[index] == -1)):
            king_moves[1L<<i] |= 1L<<(i+1)
        if (((i+7) < 64) and (file[1L<<(i+7)] - file[index] == 1)):
            king_moves[1L<<i] |= 1L<<(i+7)
        if (((i+8) < 64) and (file[1L<<(i+8)] - file[index] == 0)):
            king_moves[1L<<i] |= 1L<<(i+8)
        if (((i+9) < 64) and (file[1L<<(i+9)] - file[index] == -1)):
            king_moves[1L<<i] |= 1L<<(i+9)
        if (((i-8) > -1) and (file[1L<<(i-8)] - file[index] == 0)):
            king_moves[1L<<i] |= 1L<<(i-8)
        if (((i-9) > -1) and (file[1L<<(i-9)] - file[index] == 1)):
            king_moves[1L<<i] |= 1L<<(i-9)
        if (((i-1) > -1) and (file[1L<<(i-1)] - file[index] == 1)):
            king_moves[1L<<i] |= 1L<<(i-1)
        if (((i-7) > -1) and (file[1L<<(i-7)] - file[index] == -1)):
            king_moves[1L<<i] |= 1L<<(i-7)
    return(king_moves)

def quies(alpha, beta, position, wtm, line):
    if (position["in_check"]):
        return(alphabeta(1, alpha, beta))

    val = eval(position,wtm)
    if (val >= beta):
        return(beta)
    if (val > alpha):
        alpha = val
    cap,non_cap = generate_moves(position,wtm)
    for m in cap:
        make_move(position,m)
        val = -quies(-beta, -alpha)        
        unmake_move(position,m)
        if (val >= beta):
            return(beta)
        if (val > alpha):
            alpha = val

    return(alpha)

def remember_best_move (move,position):
    hash_index = str(self.hash_index[0:64])
    if (transition_table.has_key(hash_index)):
        transition_table[hash_index]['best_move'] = move

    
def probe_hash (depth, alpha, beta, position):
    hash_index = str(self.hash_index[0:64])

    if (transition_table.has_key(hash_index)):
        tt = transition_table[hash_index]
        if (tt['depth'] >= depth):
            if (tt['value_type'] == 'EXACT'):
                return(tt['value'])
            if (tt['value_type'] == 'ALPHA' and tt['value'] <= alpha):
                return(alpha)
            if (tt['value_type'] == 'BETA' and tt['value'] >= beta):
                return(beta)

    return(None)

def record_hash (depth, value, value_type, position):
    if (len(transition_table['key_list']) > TRANSITION_TABLE_MAX_SIZE):
        first = transition_table['key_list'].pop()
        if (transition_table.has_key(first)):
            del transition_table[first]

    hash_index = str(self.hash_index[0:64])
    transition_table[hash_index] = {}  
    transition_table[hash_index]["best_move"] = None
    transition_table[hash_index]["depth"] = depth
    transition_table[hash_index]["value"] = value
    transition_table[hash_index]["value_type"] = value_type
    transition_table["key_list"].insert(0,hash_index)

def negascout (depth, alpha, beta, position, wtm, pline, mate):
    """
    This is a slight modification of alphabeta
    called negascout.
    """
    line = []
    move_made = 0

    if (depth == 0):
        value = eval(position,wtm,depth)
        return(value)

    captures,non_captures = generate_moves(position,wtm)
    moves = captures + non_captures
    num_moves = len(moves)
    root_counter = 0

    a = alpha
    b = beta
    counter = 1
    for m in moves:
        f,t,n,c,p = m
        counters['nodes'] += 1
        if (depth == SEARCH_DEPTH):
            root_counter += 1
            if (not XBOARD):
                print "working on %s %d/%d" % \
                      (reg2san(m,position),root_counter,num_moves)
            else:
                print ".",
        #print (SEARCH_DEPTH - depth + 1) * "  ",
        #print "making move %s-%s %s %s" % (bin2alg[f],bin2alg[t],n,c)
        make_move(position,m)

        t = -negascout(depth-1, -b, -a, position, (wtm^1),
                       line, mate-10)

        if ( (t > a) and (t < beta) and (counter > 1) and \
             (depth < (SEARCH_DEPTH -1))):
            a = -negascout (depth, -beta, -t, position, (wtm^1),
                            line, mate-10)
            
        unmake_move(position,m)

        a = max(a, t)
        
        if (a >= beta):
            v,w,x,y,z = m
            print "move = ",m
            pline.insert(0,(a,bin2alg[v],bin2alg[w],x,y,z,m))
            return(a)

        b = a + 1
        counter += 1
        
    if (move_made == 0):
       if (self.in_check):
           return(-mate)
       else:
           pass
           #print 'stalemate found'

    return(a)
    
def alphabeta (depth, alpha, beta, position, wtm, pline,
               pbest_moves, mate):
    """
    This is a minimax algorithm with alpha beta prunning
    implemented in the nega-max coding style.
    """
    global CURRENT_VARIATION
    global BEST_VARIATION
    line = {}
    line["moves"] = []
    line["count"] = 0
    best_moves = []
    move_made = 0
    #value_type = "ALPHA"
    principal_variation_found = 0

    if (depth == 0):
        value = position.eval(wtm,depth)
        pline["count"] = 0
        #print "returning value",value
        return(value)

    # NULL move
    #if ((depth == STARTING_DEPTH) & (not position.in_check)):
    #    val = -alphabeta(depth-1-NULL_MOVE_REDUCTION, -beta, -beta+1, position,(wtm^1),
    #                     line, best_moves, mate-1)
    #    if (val >= beta):
    #        return(beta)


    moves = position.generate_moves(wtm)
    
    #if (depth == STARTING_DEPTH):
    #    moves = position.order_moves(moves,wtm)
    # Iterative Depening: if we are at the start of the variation,
    # we need to reorder the moves since the best moves were saved
    # at the previous depth.
    if (depth == STARTING_DEPTH and position.best_moves != []):
        best_moves = position.best_moves
        while(best_moves):
            move = best_moves.pop()
            if (move and moves.count(move) >= 1):
                moves.remove(move)
                moves.insert(0,move)
        position.best_moves = []
            
    num_moves = len(moves)
    root_counter = 0
    for m in moves:
        counters['nodes'] += 1
        if (depth == STARTING_DEPTH):
            root_counter += 1
            #if (not XBOARD):
            print "working on %s %d/%d" % (position.reg2san(m),
                                           root_counter,num_moves)

        position.make_move(m)

        if (principal_variation_found):
            val = -alphabeta(depth-1, -alpha-100, -alpha, position,(wtm^1),
                             line, best_moves, mate-10)
            if ((val > alpha) and (val < beta)):
                val = -alphabeta(depth-1, -beta, -alpha, position,(wtm^1),
                                 line, best_moves, mate-10)
        else:
            val = -alphabeta(depth-1, -beta, -alpha, position,(wtm^1),
                             line, best_moves, mate-10)

        position.unmake_move(m)

        if (val >= beta):
            return(beta)

        if (val > alpha):
            principal_variation_found = 1
            alpha = val
            pline["moves"] = list(line["moves"])
            pline["moves"].insert(0,position.reg2san(m))
            pline["count"] = line["count"] + 1
            pbest_moves.insert(0,m)

        move_made += 1

    if (move_made == 0):
       if (position.in_check):
           # it is possible that we can be checkmated in n moves
           # by the opponent in the same number of moves for us.
           # So we add a random number here.  This just forces us
           # to choose our method of being checkmated.
           r = random.randint(1,25)
           #print position
           #print "random =",r
           return(-mate-r)
       else:
           # if there are no moves and we're not in check, it's a stalemate
           return(mate/2)
           
    return(alpha)

def position2fen (position):
    piece_name = position.piece_name
    fen = ""
    empty_count = 0
    for i in range(63,-1,-1):
        index = 1L<<i
        #print i,fen
        # finish off the rank
        if ((i < 63) and ((i+1) % 8) == 0):
            if (empty_count):
                fen = "%s%s/" % (fen,empty_count)
                empty_count = 0
            else:
                fen = "%s/" % (fen)
                empty_count = 0                
        # enter a piece and put in the emptys first
        if (piece_name.has_key(index)):
            if (empty_count):
                fen = "%s%s%s" % (fen,empty_count,piece_name[1L<<i])
                empty_count = 0
            else:
                fen = "%s%s" % (fen,piece_name[1L<<i])
        else:
            empty_count += 1

        # take care of the last rank...
        if (empty_count and i == 0):
            fen = "%s%s" % (fen,empty_count)           

    return(fen)

def generate_piece_square_values ():
    piece_square_value = {}
    piece_square_value['P'] = {}
    piece_square_value['p'] = {}
    piece_square_value['N'] = {}
    piece_square_value['n'] = {}
    piece_square_value['B'] = {}
    piece_square_value['b'] = {}
    piece_square_value['R'] = {}
    piece_square_value['r'] = {}
    piece_square_value['Q'] = {}
    piece_square_value['q'] = {}
    piece_square_value['K'] = {}
    piece_square_value['k'] = {}
    piece_square_value['K_endgame'] = {}
    piece_square_value['k_endgame'] = {}
    #	White pawn.
    bp = [ 0,  0,  0,  0,  0,  0,  0,  0,
           2,  3,  4,  0,  0,  4,  3,  2, 
           4,  6, 12, 12, 12,  4,  6,  4,
           4,  7, 18, 25, 25, 16,  7,  4,
           6, 11, 18, 27, 27, 16, 11,  6,
          10, 15, 24, 32, 32, 24, 15, 10,
          10, 15, 24, 32, 32, 24, 15, 10,
           0,  0,  0,  0,  0,  0,  0,  0 ]

    wp = [ 0,  0,  0,  0,  0,  0,  0,  0,
           10, 15, 24, 32, 32, 24, 15, 10,
           10, 15, 24, 32, 32, 24, 15, 10,
            6, 11, 18, 27, 27, 16, 11,  6,
            4,  7, 18, 25, 25, 16,  7,  4,
            4,  6, 12, 12, 12,  4,  6,  4,
            2,  3,  4,  0,  0,  4,  3,  2, 
            0,  0,  0,  0,  0,  0,  0,  0 ]
        
    bn = [ -7, -3,  1,  3,  3,  1, -3, -7,
            2,  6, 14, 20, 20, 14,  6,  2,
            6, 14, 22, 26, 26, 22, 14,  6,
            8, 18, 26, 30, 30, 26, 18,  8,
            8, 18, 30, 32, 32, 30, 18,  8,
            6, 14, 28, 32, 32, 28, 14,  6,
            2,  6, 14, 20, 20, 14,  6,  2,
           -7, -3,  1,  3,  3,  1, -3, -7]

    wn = [ -7, -3,  1,  3,  3,  1, -3, -7,
            2,  6, 14, 20, 20, 14,  6,  2,
            6, 14, 28, 32, 32, 28, 14,  6,
            8, 18, 30, 32, 32, 30, 18,  8,
            8, 18, 26, 30, 30, 26, 18,  8,
            6, 14, 22, 26, 26, 22, 14,  6,
            2,  6, 14, 20, 20, 14,  6,  2,
           -7, -3,  1,  3,  3,  1, -3, -7]

    bb = [16, 16, 16, 16, 16, 16, 16, 16,
          26, 29, 31, 31, 31, 31, 29, 26,
          26, 28, 32, 32, 32, 32, 28, 26,
          16, 26, 32, 32, 32, 32, 26, 16,
          16, 26, 32, 32, 32, 32, 26, 16,
          16, 28, 32, 32, 32, 32, 28, 16,
          16, 29, 31, 31, 31, 31, 29, 16,
          16, 16, 16, 16, 16, 16, 16, 16]

    wb = [16, 16, 16, 16, 16, 16, 16, 16,
          16, 29, 31, 31, 31, 31, 29, 16,
          16, 28, 32, 32, 32, 32, 28, 16,
          16, 26, 32, 32, 32, 32, 26, 16,
          16, 26, 32, 32, 32, 32, 26, 16,
          26, 28, 32, 32, 32, 32, 28, 26,
          26, 29, 31, 31, 31, 31, 29, 26,
          16, 16, 16, 16, 16, 16, 16, 16]

    br = [ 0,  0,  0,  3,  3,  0,  0,  0,
          -2,  0,  0,  0,  0,  0,  0, -2,
          -2,  0,  0,  0,  0,  0,  0, -2,
          -2,  0,  0,  0,  0,  0,  0, -2,
          -2,  0,  0,  0,  0,  0,  0, -2,
          -2,  0,  0,  0,  0,  0,  0, -2,
          10, 10, 10, 10, 10, 10, 10, 10,
           0,  0,  0,  0,  0,  0,  0,  0]

    wr = [ 0,  0,  0,  0,  0,  0,  0,  0,
          10, 10, 10, 10, 10, 10, 10, 10,
          -2, 0, 0, 0, 0, 0, 0, -2,
          -2, 0, 0, 0, 0, 0, 0, -2,
          -2, 0, 0, 0, 0, 0, 0, -2,
          -2, 0, 0, 0, 0, 0, 0, -2,
          -2, 0, 0, 0, 0, 0, 0, -2,
          0, 0, 0, 3, 3, 0, 0, 0]

    bq = [-2, -2, -2, 0, 0, -2, -2, -2,
          0, 0, 1, 1, 1, 0, 0, 0,
          0, 1, 1, 1, 1, 0, 0, 0,
          0, 0, 0, 2, 2, 0, 0, 0,
          0, 0, 0, 2, 2, 0, 0, 0,
          -2, -2, 0, 0, 0, 0, 0, 0,
          -2, -2, 0, 0, 0, 0, 0, 0,
          -2, -2, 0, 0, 0, 0, 0, 0]

    wq = [-2, -2, 0, 0, 0, 0, 0, 0,
          -2, -2, 0, 0, 0, 0, 0, 0,
          -2, -2, 0, 0, 0, 0, 0, 0,
          0, 0, 0, 2, 2, 0, 0, 0,
          0, 0, 0, 2, 2, 0, 0, 0,
          0, 1, 1, 1, 1, 0, 0, 0,
          0, 0, 1, 1, 1, 0, 0, 0,
          -2, -2, -2, 0, 0, -2, -2, -2]

    bk = [3, 3, 8, -12,-8, -12,10, 5,
          -5, -5, -12,-12,-12,-12,-5, -5,
          -7, -15,-15,-15,-15,-15,-15,-7,
          -20,-20,-20,-20,-20,-20,-20,-20,
          -20,-20,-20,-20,-20,-20,-20,-20,
          -20,-20,-20,-20,-20,-20,-20,-20,
          -20,-20,-20,-20,-20,-20,-20,-20,
          -20,-20,-20,-20,-20,-20,-20,-20]

    wk = [-20,-20,-20,-20,-20,-20,-20,-20,
          -20,-20,-20,-20,-20,-20,-20,-20,
          -20,-20,-20,-20,-20,-20,-20,-20,
          -20,-20,-20,-20,-20,-20,-20,-20,
          -20,-20,-20,-20,-20,-20,-20,-20,
          -7, -15,-15,-15,-15,-15,-15, -7,
          -5,  -5,-12,-12,-12,-12, -5, -5,
           3,   3,  8,-12, -8,-12, 10,  5]

    bk_endgame = [0, 0, 1, 2, 2, 1, 0, 0,
                  0, 2, 4, 5, 5, 4, 2, 0,
                  1, 4, 6, 7, 7, 6, 4, 1,
                  1, 4, 10, 10, 10, 10, 4, 1,
                  1, 4, 12, 15, 15, 12, 4, 1,
                  0, 7, 10, 12, 12, 10, 7, 0,
                  0, 2, 4, 5, 5, 4, 2, 0, 
                  0, 0, 0, 0, 0, 0, 0, 0]
    
    wk_endgame = [0, 0, 0, 0, 0, 0, 0, 0, 
                  0, 2, 4, 5, 5, 4, 2, 0,
                  0, 7, 10, 12, 12, 10, 7, 0,
                  1, 4, 12, 15, 15, 12, 4, 1,
                  1, 4, 10, 10, 10, 10, 4, 1,
                  1, 4, 6, 7, 7, 6, 4, 1,
                  0, 2, 4, 5, 5, 4, 2, 0,
                  0, 0, 1, 2, 2, 1, 0, 0]

    for i in range(64):
        piece_square_value['P'][1L<<i] = wp[63-i]
        piece_square_value['p'][1L<<i] = bp[63-i]
        piece_square_value['N'][1L<<i] = wn[63-i]
        piece_square_value['n'][1L<<i] = bn[63-i]
        piece_square_value['B'][1L<<i] = wb[63-i]
        piece_square_value['b'][1L<<i] = bb[63-i]
        piece_square_value['R'][1L<<i] = wr[63-i]
        piece_square_value['r'][1L<<i] = br[63-i]
        piece_square_value['Q'][1L<<i] = wq[63-i]
        piece_square_value['q'][1L<<i] = bq[63-i]
        piece_square_value['K'][1L<<i] = wk[63-i]
        piece_square_value['k'][1L<<i] = bk[63-i]
        piece_square_value['K_endgame'][1L<<i] = wk_endgame[63-i]
        piece_square_value['k_endgame'][1L<<i] = bk_endgame[63-i]

    return(piece_square_value)

def generate_book (book_filename=None,binbook_filename=None,max_moves=19):
    """
    This function is used to generate the opening book.
    It works by recording moves from a game file in a hash table.
    The hash table is then read into memory and used directly.
    """
    if (not book_filename or not binbook_filename):
        print "Error: missing book filename"
    try:
        fd = open(book_filename)
        fd.close()
    except:
        print "Error reading",book_filename
        return
    print "\nGenerating book moves from",book_filename,
    illegal_moves = 0
    game_count = 0
    move_count = 0
    game_move_count = 0
    ignore_restofgame = 0
    position = None
    line_count = 0

    for i in open(book_filename):
        line = i.strip()
        line_count += 1
        if (line.find("White") == 1 or line.find("ECO") == 1):

            print "game=%s line=%s" % (game_count,line_count)    

            position = get_fen_position(INIT_FEN)
            game_count += 1
            wtm  = 0
            game_move_count = 0
            ignore_restofgame = 0
        if (line_count % 5000 == 0):
            # dump the book every 5000 lines
            bd = open(binbook_filename,"w")
            cPickle.dump(book,bd)
            bd.close()
            print "dumped opening book"

        if (line and line[0] != '['):
            moves = line.split()
            for move in moves:
                # ignore move numbers
                promoted_piece = ""
                if (move.find(".") == -1):
                    wtm ^= 1
                    c,nc = generate_moves(position,wtm)
                    legal_moves = get_move_list(c + nc,position)
                    # strip off the + or ++ for check and checkmate
                    if (move.find('+') > -1):
                        index = move.find("+")
                        move = move[0:index]

                    if (move.find('=') > -1):
                        index = move.find("=")
                        promoted_piece = move[index+1:index+2]
                        move = move[0:index+1]

                    # make the move
                    if (not ignore_restofgame and legal_moves.has_key(move)):
                        if (not promoted_piece):
                            bmove = legal_moves[move]

                        else:
                            # for a promotion, we need to promote to the
                            # correct piece
                            f,t,n,c,p = legal_moves[move]
                            bmove = (f,t,n,c,promoted_piece)

                        move_count += 1
                        game_move_count += 1

                        if (game_move_count > max_moves):
                            ignore_restofgame = 1
                        fen = position2fen(position)
                        book_index = "%s:%s" % (fen,wtm) 
                        if (book.has_key(book_index)):
                            # before adding the move make sure it's unique
                            if (move in book[book_index]):
                                pass
                            else:
                                book[book_index].append(move)
                        else:
                            book[book_index] = []
                            book[book_index].append(move)
                        position = make_move(position,bmove)

                    elif (move in ["1-0","0-1","1/2-1/2"]):
                        pass
                        #print "Game Over",line_count
                    elif (not ignore_restofgame):
                        display(position)
                        print "Invalid move",move
                        print "line",line_count

                        illegal_moves += 1
                        # might as well save what we have so far
                        bd = open(binbook_filename,"w")
                        cPickle.dump(book,bd)
                        bd.close()
                        sys.exit()
                else:
                    pass

    print "\ngenerate_book: pgn file %s games=%s legal_moves=%s illegal_moves=%s lines=%s" % \
          (book_filename,game_count,move_count,illegal_moves,line_count)

    bd = open(binbook_filename,"w")
    cPickle.dump(book,bd)
    bd.close()
    return

def analyze_game (game_filename=None,max_moves=10000):
    if (not game_filename):
        print "Error: missing game filename"
        return
    print "\nAnalyzing game",game_filename,
    illegal_moves = 0
    game_count = 0
    move_count = 0
    game_move_count = 0
    ignore_restofgame = 0
    position = None
    line_count = 0

    for i in open(game_filename):
        line = i.strip()
        line_count += 1

        if (line.find("White") == 1 or line.find("ECO") == 1):
            print "game=%s line=%s" % (game_count,line_count)     #"."

            position = get_fen_position(INIT_FEN)
            game_count += 1
            wtm = 0
            game_move_count = 0
            ignore_restofgame = 0
 
        if (line and line[0] != '['):
            moves = line.split()
            for move in moves:
                # ignore move numbers
                promoted_piece = ""
                if (move.find(".") == -1):
                    wtm ^= 1
                    c,nc = generate_moves(position,wtm)
                    legal_moves = get_move_list(c + nc,position)
                    print "legal moves",display_moves(c+nc)
                    print "san moves", get_move_list(c+nc,position)
                    # strip off the + or ++ for check and checkmate
                    if (move.find('+') > -1):
                        index = move.find("+")
                        move = move[0:index]
                    if (move.find('=') > -1):
                        index = move.find("=")
                        promoted_piece = move[index+1:index+2]
                        move = move[0:index+1]
                        # we need to insert the promoted piece into
                        # the legal move
                    if (not ignore_restofgame and legal_moves.has_key(move)):
                        if (not promoted_piece):
                            bmove = legal_moves[move]
                        else:
                            # for a promotion, we need to promote to the
                            # correct piece
                            f,t,n,c,p = legal_moves[move]
                            bmove = (f,t,n,c,promoted_piece)
                        move_count += 1
                        game_move_count += 1
                        if (game_move_count > max_moves):
                            ignore_restofgame = 1
                        fen = position2fen(position)

                        position = make_move(position,bmove)
                        display(position)

                    elif (move in ["1-0","0-1","1/2-1/2"]):
                        pass

                    elif (not ignore_restofgame):
                        display(position)
                        print "Invalid move",move
                        print "line",line_count
                        illegal_moves += 1
                        # might as well save what we have so far
                        sys.exit()
                else:
                    pass
                    #print "move number ",move
    print "\nanalyze_game: pgn file %s games=%s legal_moves=%s illegal_moves=%s lines=%s" % \
          (game_filename,game_count,move_count,illegal_moves,line_count)
    #bindex = book.keys()
    return

def search_simple (position, wtm):
    move_list = position.generate_moves(wtm)
    moves,san_moves = position.get_move_list(move_list)
    print move_list
    print moves
    print san_moves
    if (len(move_list) > 0):
        return(san_moves[move_list[0]])
    else:
        return("")
    
def search_alphabeta (position,wtm):
    #print "thinking..."
    global START_TIME
    global STARTING_DEPTH
    START_TIME = time.time()

    for depth in range(3,SEARCH_DEPTH+1): #(3, SEARCH_DEPTH+1): 
        line = {}
        line["moves"] = []
        line["count"] = 0
        best_moves = []
        STARTING_DEPTH = depth
        counters['nodes'] = 0
        start = time.time()
        val = alphabeta(depth,-INFINITY,INFINITY,position,
                        wtm,line, best_moves, MATE)
        end = time.time()

        if (len(best_moves) == 0):
            regular_move = ""
        else:
            if (not XBOARD):
                print "Best moves:",
                for m in best_moves:
                    print "%s " % (position.reg2san(m)),
                print

                print "Best variation:", 
                for m in line["moves"]:
                    print m, 
                print
            regular_move = "%s%s" % (bin2alg[best_moves[0].from_square],
                                     bin2alg[best_moves[0].to_square])
            # at this point, we save the best moves for the next depth
            position.best_moves = best_moves

        # no point in going on if there is a winner.
        if (position.winner):
            return(regular_move)
        
        #if (not XBOARD):
        print "depth=%s move=%s value=%s nps=%d total nodes=%s time=%6.2f" % \
              (depth,regular_move,val,counters['nodes']/(end-start),
               counters['nodes'],end-start)

    return(regular_move)

def search_negascout (position,wtm):
    global START_TIME
    START_TIME = time.time()

    for depth in range(SEARCH_DEPTH, SEARCH_DEPTH+1):
        line = []
        counters['nodes'] = 0
        start = time.time()
        val = negascout(depth,-INFINITY,INFINITY,position,
                        wtm,line,MATE)
        end = time.time()
        if (len(line) == 0):
            regular_move = ""
        else:
            v,f,t,n,c,p,m = line[0]
            regular_move = "%s%s" % (f,t)
            remember_best_move(m,position)
        print "depth=%s move=%s value=%s nps=%d total nodes=%s time=%6.2f" % \
              (depth,regular_move,val,counters['nodes']/(end-start),
               counters['nodes'],end-start)

    return(regular_move)

def check_end_of_game (position,moves):
    if (moves == [""] or moves == [] or moves == ""):
        moves = None

    if (moves == None and not position.in_check):
        print "1/2-1/2 {Stalemate}"
        return(1)
    if (moves == None and position.in_check):
        if (position.side_in_check): # computer is white
            print "0-1 {Black mates}"
        else:
            print "1-0 {White mates}"
        #print "Game over.  Winner is",position.winner
        return(1)

    return(0)

def print_move_list (position):
    # list makes a copy because we don't want
    # to change the actual history.
    history = list(position.move_history)
    print "\nGame Record\n====================="
    if (len(history) % 2 != 0):
        history.append(("",""))

    counter = 1
    for i in range(0,len(history),2):
        print "%s. %s\t\t%s" % (counter,history[i][0],history[i+1][0])
        counter += 1
    return

def reset_game ():
    position = Position()
    computer_color = 0
    counters['nodes'] = 0
    if (not XBOARD):
        print_help()
    return(position)
    
def let_computer_move (position,computer_color):
    moves = position.generate_moves(computer_color)
    moves,san_moves = position.get_move_list(moves)
    if (check_end_of_game(position,moves)):
        return(position)
    
    fen = position2fen(position)
    bindex = "%s:%s" % (fen,computer_color)
    if (book.has_key(bindex)):
        random_index = random.randint(0,len(book[bindex])-1)
        book_move = book[bindex][random_index]
        move = moves[book_move]
        regular_move = "%s%s" % (bin2alg[move.from_square],bin2alg[move.to_square])

        if (not XBOARD):
            print "found book move"
    else:
        if (len(moves) == 1):
            # there is only one move...just make it
            m = moves[0]
            regular_move = "%s%s" % (bin2alg[m.from_square],bin2alg[m.to_square])
        else:
            regular_move = search_alphabeta(position,computer_color)
            #regular_move = search_simple(position,computer_color)

        if (check_end_of_game(position,regular_move)):
            return(position)

        if (moves.has_key(regular_move)):
            move = moves[regular_move]
        else:
            print "invalid computer move",regular_move
            return(position)

    print "move %s" % \
          (san_moves[regular_move]) 
    position.move_history.append((san_moves[regular_move],move))

    position.make_move(move)
    position.move_count += 1
    if (not XBOARD):
        print position

    return(position)

def print_help ():
    print "Shatranj version",VERSION
    print "       go or pass: switch sides      m: show legal moves" 
    print "                n: new game          l: list game record"
    print "                d: display board     k: show book moves"  
    print "           sd <n>: search depth <n>  b: take back last move"
    print "                e: show current position evaluation value"
    print "           remove: take back last two moves"
    print " resign or result: resign and end the game"
    print "              fen: show the current board postion in FEN notation"
    print "           v or h: help              q: quit"
    return

def play ():
    global SEARCH_DEPTH
    global XBOARD
    force = 0
    position = Position()
    command = ""
    counters['nodes'] = 0

    if(not XBOARD):
        print_help()
    else:
        print 'feature myname="Shatranj',VERSION,'"'
        print "feature ping=1"
        print "feature san=1"
        print "feature time=0"
        print "feature done=1"
        print "ok"

    computer_color = 0
    while (command != "quit"):
        move_list= position.generate_moves(computer_color^1)
        moves,san_moves = position.get_move_list(move_list)

        if (check_end_of_game(position,moves)):
            print_move_list(position)
            position = reset_game()

        if (not XBOARD):
            print "\nShatranj (%s to move):" % (mover[computer_color^1]),
        try:
            command = raw_input()
        except EOFError:
            goodbye("EOFError")
        except IOError:
            print "got IOError"
            continue
        if (len(command) == 1 and command[0:1] == "d"):
            print position
        elif (len(command) == 1 and command[0:1] == "k"):
            fen = position2fen(position)
            bindex = "%s:%s" % (fen,computer_color^1)
            if (book.has_key(bindex)):
                book_moves = book[bindex]
                book_moves.sort()
                print "book moves:",
                for i in book_moves:
                    print i,
                print
            else:
                print "Sorry, no book moves available."

        # help
        elif (len(command) == 1 and command[0:1] == "h"):
            print_help()

        elif (len(command) == 1 and command[0:1] == "v"):
            print_help()

        # take back last move
        elif (len(command) == 1 and command[0:1] == "b"):

            if (len(position.move_history) < 1):
                print "no moves to take back"
            else:
                san_move,move = position.move_history.pop()
                position.unmake_move(move)
                position.move_count -= 1
                print "took back %s" % (san_move)
                print position
                computer_color ^= 1

        # take back last two moves
        elif (command[0:6] == "remove"):

            if (len(position.move_history) < 2):
                print "no moves to take back"
            else:
                san_move,move = position.move_history.pop()
                position.unmake_move(move)
                position.move_count -= 1
                san_move,move = position.move_history.pop()
                position.unmake_move(move)
                position.move_count -= 1
                print "ok"
                
        elif (command[0:4] == "ping"):
            print "pong %s" % (command[5:])

        # Go or Pass: force the computer to play the move
        elif (command[0:2] == "go" or command[:4] == "pass"):
            computer_color ^= 1
            print "ok"
            force = 0
            position = let_computer_move(position,computer_color)

        elif (command[0:5] == "force"):
            print "ok"
            force = 1

        elif (command[0:6] == "xboard"):
            XBOARD = 1
            print 'feature myname="Shatranj',VERSION,'"'
            print "feature ping=1"
            print "feature san=1"
            print "feature time=0"
            print "feature done=1"
            print "feature colors=0"
            print "feature playother=1"
            print "ok"
            
        elif (command[0:8] == "protover" or command[0:8] == "computer" or \
              command[0:6] == "random" or \
              command[0:4] == "time" or command[0:4] == "otim" or \
              command[0:5] == "level" or command[0:4] == "hard" or \
              command[0:8] == "accepted" or command[0:4] == "easy" or \
              command[0:5] == "white" or command[0:5] == "black"): 
            print "debug: got ",command
            print "ok"

        # resign game
        elif (command[0:6] == "result" or command[0:6] == "resign"):
            position = Position()
            computer_color = 0
            counters['nodes'] = 0
            #print "Player resigns.  Thanks for playing!"
            if (not XBOARD):
                print_help()

        # start new game
        elif (command[0:1] == "n"):
            position = reset_game()
            print "ok"
            
        elif (command[0:2] == "st"):
            print "ok"

        # change the search depth
        elif (command[0:2] == "sd"):
            temp = command.split(" ")
            if (len(temp) != 2):
                print "Invalid search depth: currently set to",SEARCH_DEPTH
            else:
                sd = temp[1]
                SEARCH_DEPTH = int(sd)
                print "sd = %s" % SEARCH_DEPTH

        # list the move history
        elif (command[0:1] == "l"):
            print_move_list(position)
            
        # show possible moves
        elif (command[0:1] == "m"):
            print "\nlegal moves:",
            move_list = san_moves.values()
            move_list.sort()
            for i in move_list:
                print i,

        # show static evaluation
        elif (len(command) == 1 and command[0:1] == "e"):
            print "\nBoard evaluation: ",position.eval(computer_color,0)

        elif (command[:8] == "setboard"):
            try:
                position= Position(command[9:].strip())
                computer_color=0
                counters['nodes'] = 0
            except:
                print "Invalid setboard command: usage is setboard <fen position>"
       
        elif (command[:3]=="fen"):
            print "FEN Position: ",position2fen(position)

        # quit the game
        elif (command[0:1] == "q"):
            goodbye("Quiting")

        else:
            promoted_piece = ""
            # if there's a promotion (entered with an = sign
            # we need to add the promoted piece to the move.
            if (command.find("=") > 0):
                index = command.find("=")
                print "promotion move..",command
                try:
                    promoted_piece = command[index+1:index+2]
                except:
                    print "Warning: in the future, please specify promotion piece (i.e. f8=Q)"
                    print "         Defaulting to promoting pawn to queen."
                    promoted_piece = ""
                command = command[0:index+1]
                # we need to insert the promoted piece into
                # the legal move
                print "  new move=%s promoted_piece=%s" % \
                      (command,promoted_piece)

            # some moves have a check sign (+ for check or ++ for mate) so we need to remove it first
            if (command.find("+") > 0):
                index = command.find("+")
                command = command[0:index]
            
            # some moves have a hash sign (#) for checkmate so we need to remove it first
            if (command.find("#") > 0):
                index = command.find("#")
                command = command[0:index]
            

            if (moves.has_key(command)):
                line = []
                m = moves[command]
                regular_move = "%s%s" % (bin2alg[m.from_square],bin2alg[m.to_square])
                if (not promoted_piece):
                    move = moves[command]
                else:
                    # for a promotion, we need to promote to the
                    # correct piece
                    move = moves[command]
                    move.promoted_piece = promoted_piece

                position.move_history.append((san_moves[regular_move],move))

                position.make_move(move)
                position.move_count += 1
                counters['nodes'] = 0
                # force is there for xboard.  force means to stop letting computer play
                if (not force):
                    let_computer_move(position,computer_color)
                else:
                    computer_color ^= 1
            else:
                print "Illegal move:",command
                print "legal moves:",
                move_list = san_moves.values()
                move_list.sort()
                for i in move_list:
                    print i,

    return

def goodbye (message=""):
    print "\nGoodbye with message %s\n" % message
    sys.exit()
    return

def gotSIGINT (signum,frame):
    #print "\nGoodbye\n"
    #sys.exit()
    print "gotSIGINT: got signum %s with frame %s" % (signum, frame)
    return

def gotSIGTERM (signum,frame):
    #print "\nGoodbye\n"
    print "gotSIGTERM: got signum %s with frame %s" % (signum, frame)
    sys.exit()
    return

def gotSIGHUP (signum,frame):
    #print "\nGoodbye\n"
    print "gotSIGHUP: got signum %s with frame %s" % (signum, frame)
    #sys.exit()
    return

#############################################################
# These are various test functions used to get the bugs out #
#############################################################
def test_init ():
    global tests_passed, tests_failed, test_number
    p = Position()
    print "1. test: initialization"
    bb = p.piece_bb
    if ((bb['k'] == e8) and (bb['q'] == d8) and (bb['b'] == (c8|f8)) and \
        (bb['n'] == (b8|g8)) and (bb['r'] == (a8|h8)) and (bb['p'] == (255<<48)) and \
        (bb['K'] == e1) and (bb['Q'] == d1) and (bb['B'] == (c1|f1)) and \
        (bb['N'] == (b1|g1)) and (bb['R'] == (a1|h1)) and (bb['P'] == (255<<8))):  
        print "    1.1 pieces in correct place: PASSED"
        tests_passed += 1
    else:
        print "    1.1 pieces in correct place: FAILED"
        tests_failed += 1
    return

def test_checkmate ():
    global SEARCH_DEPTH
    global tests_passed, tests_failed, test_number
    SEARCH_DEPTH = 3
    wtm = 1
    fen = "1k6/pp3R2/6pp/4p3/2B3b1/4Q3/PPP2B2/3rK3"
    p = Position(fen)
    print p
    m =  search_alphabeta(p,wtm)
    print "6. test: checkmate"
    if (m == '' and p.winner == "black"):
        print "    6.1 checkmate test black checkmate: PASSED"
        tests_passed += 1
    else:
        print "    6.1 checkmate test black checkmate: FAILED"
        tests_failed += 1

def test_pinned ():
    global tests_passed, tests_failed, test_number
    fen = "4r1k1/p4pp1/3q3p/5P2/4b2Q/7P/P1r3PK/4RR2"
    wtm = 1
    p = Position(fen)
    p.w_king_move_count = 2
    p.b_king_move_count = 3
    p.w_rook_a1_move_count = 2
    p.w_rook_h1_move_count = 2
    p.b_rook_a8_move_count = 2
    p.b_rook_h8_move_count = 2
    p.w_rook_a1_location = e1
    p.w_rook_h1_location = f1
    p.b_rook_a8_location = c2
    p.b_rook_h8_location = e8
    print "5. test: pinned piece check"
    #print p
    p.generate_attacks()
    mask = p.pinned(g2,1)
    move_list = p.generate_moves(1)
    moves,san_moves = p.get_move_list(move_list)
    if (mask == (255<<8)):
        print "    5.1 pinned g2 pawn mask correct: PASSED"
        tests_passed += 1
    else:
        print "    5.1 pinned g2 pawn mask not correct: FAILED"
        tests_failed += 1
 
    if (san_moves.values() == ['Qf4', 'Rf4', 'Qg3', 'Kg1', 'Kh1']):
        print "    5.2 king in check moves correct: PASSED"
        tests_passed += 1
    else:
        print "    5.2 king in check moves not correct: FAILED"
        tests_failed += 1

    p = Position("rnbqk2r/ppp2ppp/4p3/8/6n1/6P1/PbPQ1PBP/RNBK2NR")
    moves = p.show_moves(1)
    moves.sort()
    # Queen is pinned to D file
    correct_moves = ['Bc6', 'Bd5', 'Be4', 'Bf1', 'Bf3', 'Bh3', 'Bxb2', 'Bxb7',
                     'Ke1', 'Ke2', 'Na3', 'Nc3', 'Ne2', 'Nf3', 'Nh3',
                     'Qd3', 'Qd4', 'Qd5', 'Qd6', 'Qd7', 'Qxd8',
                     'a3', 'a4', 'c3', 'c4', 'f3', 'f4', 'h3', 'h4']
    if (moves == correct_moves):
        print "    5.3 Queen d2 pinned moves correct: PASSED"
        tests_passed += 1
    else:
        print "    5.3 Queen d2 pinned moves not correct: FAILED"
        tests_failed += 1

def test_alphabeta (game_file=None):
    global SEARCH_DEPTH
    SEARCH_DEPTH = 5
    fd = open(game_file)
    lines = fd.readlines()
    for line in lines:
        t = line.split()
        #print "fen=%s" % t[0]
        print 40*"#","\nmover=%s correct move=%s" % \
              (t[1],t[5])
        fen = t[0]
        correct_move = t[5]
        if (t[1] == "b"):
            wtm = 0
        else:
            wtm = 1
            
        position = get_fen_position(fen)
        position.w_king_move_count = 1
        position.b_king_move_count = 1
        position.w_rook_moved = {h1:1, a1:1}
        position.b_rook_moved = {h8:1, a8:1}
        c,nc = generate_moves(position,wtm)
        moves = position.get_move_list(c+nc)

        display(position)
        start = time.time()
        counters['nodes'] = 0
        line = []
        val = alphabeta(SEARCH_DEPTH,-INFINITY,INFINITY,position,wtm,line,MATE)
        end = time.time()
        print "value=%s nps=%d total nodes=%s time=%6.2f" % \
              (val,counters['nodes']/(end-start),counters['nodes'],end-start)
        if (len(line) == 0):
            print "no move found"
            continue
        else:
            v,f,t,n,c,p = line[0]

            move = "%s%s" % (f,t)        
            if (moves.has_key(move)):
                move = moves[move]
            else:
                print "invalid computer move",move
                continue
            print "computer move %s  best move %s" % \
                  (reg2san(move,position),correct_move)

def test_generate_moves ():
    global tests_passed, tests_failed, test_number  
    fen = "2q1r1k1/1ppb4/r2p1Pp1/p4n1p/2P1n3/5NPP/PP3Q1K/2BRRB2"
    p = Position(fen)
    print p
    move_list = p.generate_moves(wtm=1)
    moves,san_moves = p.get_move_list(move_list)
    san = san_moves.values()
    san.sort()
    print "7. test: move generation"
    if (san == ['Bd2', 'Bd3', 'Be2', 'Be3', 'Bf4', 'Bg2', 'Bg5',
                'Bh6', 'Kg1', 'Kg2', 'Kh1', 'Nd2', 'Nd4', 'Ne5',
                'Ng1', 'Ng5', 'Nh4', 'Qa7', 'Qb6', 'Qc2', 'Qc5',
                'Qd2', 'Qd4', 'Qe2', 'Qe3', 'Qg1', 'Qg2', 'Rd2',
                'Rd3', 'Rd4', 'Rd5', 'Re2', 'Re3', 'Rxd6', 'Rxe4',
                'a3', 'a4', 'b3', 'b4', 'c5', 'f7', 'g4', 'h4']):
        print "    7.1 white move generation test: PASSED"
        tests_passed += 1
    else:
        print "    7.1 white move generation test: FAILED"
        tests_failed += 1

    move_list = p.generate_moves(wtm=0)
    moves,san_moves = p.get_move_list(move_list)
    san = san_moves.values()
    san.sort()
    if (san == ['Ba4', 'Bb5', 'Bc6', 'Be6', 'Kf7', 'Kf8', 'Kh7',
                'Kh8', 'Nc3', 'Nc5', 'Nd2', 'Nd4', 'Ne3', 'Ne7',
                'Nexg3', 'Nfxg3', 'Ng5', 'Ng7', 'Nh4', 'Nh6', 'Nxf2',
                'Nxf6', 'Qa8', 'Qb8', 'Qd8', 'Ra7', 'Ra8', 'Rb6',
                'Rc6', 'Rd8', 'Re5', 'Re6', 'Re7', 'Rf8', 'a4', 'b5',
                'b6', 'c5', 'c6', 'd5', 'g5', 'h4']):
        print "    7.2 black move generation test: PASSED"
        tests_passed += 1
    else:
        print "    7.2 black move generation test: FAILED"
        tests_failed += 1

    p = Position("r3r1k1/p1p2ppp/7q/3p4/4b3/4P1PK/PP5P/R1B1Q1R1")
    print p
    san = p.show_moves(1)
    san.sort()
    print "7. test: pawn move generation"
    if (san == ['Kg4']):
        print "    7.3 pawn move generation test: PASSED"
        tests_passed += 1
    else:
        print "    7.3 pawn move generation test: FAILED"
        tests_failed += 1


def test_repetition ():
    global tests_passed, tests_failed, test_number
    p = Position()
    print "4. test: repetition check"
    p.make_move(Move(b1,c3,"","",""))
    p.make_move(Move(b8,c6,"","",""))
    p.make_move(Move(g1,f3,"","",""))
    p.make_move(Move(g8,f6,"","",""))

    hash_index = str(p.hash_index[:64])
    current_array = p.position_counter_array_list[-1]
    if (current_array.has_key(hash_index) and \
        current_array[hash_index] == 1):
        print "    4.1 repetition check a: PASSED"
        tests_passed += 1
    else:
        print "    4.1 repetition check a: FAILED"
        tests_failed += 1

    p.make_move(Move(c3,b1,"","",""))
    p.make_move(Move(b1,c3,"","",""))
    hash_index = str(p.hash_index[:64])
    current_array = p.position_counter_array_list[-1]

    if (current_array.has_key(hash_index) and \
        current_array[hash_index] == 2):
        print "    4.2 repetition check b: PASSED"
        tests_passed += 1
    else:
        print "    4.2 repetition check b: FAILED"
        tests_failed += 1
 
def test_generate_attacks ():
    global tests_passed, tests_failed, test_number
    
    fen = "Rr2k2r/2NP2P1/r3R3/Pp3PpB/1pPpn3/5NPP/PP1B1Qp1/RB2KN1R"
    p = Position(fen)
    print p
    p.b_pawn_last_double_move = b5
    p.generate_attacks()
    display(p.attacks_to[b5])
    display(p.attacks_to[e8])
    display(p.attacks_from[d2])
    print "3. test: generating attacks"
    if (p.attacks_to[b5] == (a5|c4|c7|b8)):
        print "    3.1 attacks to b5: PASSED"
        tests_passed += 1
    else:
        print "    3.1 attacks to b5: FAILED"
        tests_failed += 1

    if (p.attacks_to[e8] == (b8|c7|d7|e6|h5|h8)):
        print "    3.2 attacks to e8: PASSED"
        tests_passed += 1
    else:
        print "    3.2 attacks to e8: FAILED"
        tests_failed += 1

    if (p.attacks_from[d2] == (c1|c3|b4|e1|e3|f4|g5)):
        print "    3.3 attacks from d2: PASSED"
        tests_passed += 1
    else:
        print "    3.3 attacks from d2: FAILED"
        tests_failed += 1

def test_search ():
    global SEARCH_DEPTH
    global tests_passed, tests_failed, test_number
    SEARCH_DEPTH = 3
    p = Position("1rb2rk1/4R1p1/1pqn1pBp/3p4/5Q2/1NP3PP/6PK/4R3")
    p.w_king_move_count = 2
    p.b_king_move_count = 3
    p.w_rook_a1_move_count = 2
    p.w_rook_h1_move_count = 2
    p.b_rook_a8_move_count = 2
    p.b_rook_h8_move_count = 2
    p.w_rook_a1_location = e1
    p.w_rook_h1_location = e7
    p.b_rook_a8_location = b8
    p.b_rook_h8_location = f8
    move =  search_alphabeta(p,1)
    print "2. test: alphabeta search"
    if (move == 'e1c1'):
        print "    2.1 alphabeta search: PASSED"
        tests_passed += 1
    else:
        print "    2.1 alphabeta search: FAILED"
        tests_failed += 1

def test_castling ():
    global SEARCH_DEPTH
    global tests_passed, tests_failed, test_number
    p = Position("1rb2rk1/6p1/1pqn1pBp/3p4/5Q2/1NP3PP/8/R3K2R")
    print p
    print "8. test: castling"
    move_list = p.generate_moves(wtm=1)
    moves,san_moves = p.get_move_list(move_list)
    san = san_moves.values()
    
    if ('O-O' in san and 'O-O-O' in san):
        print "    8.1 castling moves: PASSED"
        tests_passed += 1
    else:
        print "    8.1 castling moves: FAILED"
        tests_failed += 1

    move = moves['O-O']
    p.make_move(move)
    if (p.piece_name[f1] == 'R' and p.piece_name[g1] == 'K'):
        print "    8.2 castling king side: PASSED"
        tests_passed += 1
    else:
        print "    8.2 castling king side: FAILED"
        tests_failed += 1

    p.unmake_move(move)

    move = moves['O-O-O']
    p.make_move(move)
    if (p.piece_name[d1] == 'R' and p.piece_name[c1] == 'K' and p.piece_name[h1] == 'R'):
        print "    8.3 castling queen side: PASSED"
        tests_passed += 1
    else:
        print "    8.3 castling queen side: FAILED"
        tests_failed += 1

def test_check ():
    global SEARCH_DEPTH
    global tests_passed, tests_failed, test_number
    SEARCH_DEPTH = 5
    wtm = 0
    fen = "r1bk1R1r/1p1p2p1/p2Qp2p/2P1N3/P7/1P1B4/2P3KP/5R2"
    p = Position(fen)
    p.w_king_move_count = 2
    p.b_king_move_count = 1
    p.w_rook_a1_move_count = 2
    p.w_rook_h1_move_count = 2
    p.b_rook_a8_move_count = 0
    p.b_rook_h8_move_count = 0
    p.w_rook_a1_location = f1
    p.w_rook_h1_location = f8
    p.b_rook_a8_location = a8
    p.b_rook_h8_location = h8
    p.in_check = 1
    print p
    m =  search_alphabeta(p,wtm)
    print "9. test: check"
    print "m=",m
    if (m == 'h8f8'):
        print "    9.1 check test black checkmate: PASSED"
        tests_passed += 1
    else:
        print "    9.1 check test black checkmate: FAILED"
        tests_failed += 1
    # check to make sure we can get out of check by capturing
    # and promoting a pawn.
    p =  Position("8/2p1kp1p/2p3p1/8/8/6P1/3p3P/4R2K")
    m = p.show_moves(0)
    print m
    if ('dxe1=' in m):
        print "    9.2 In check promotion capture test: PASSED"
        tests_passed += 1
    else:
        print "    9.2 :In check promotion capture test: FAILED"
        tests_failed += 1
        

def test_checkmated ():
    global SEARCH_DEPTH
    global tests_passed, tests_failed, test_number
    SEARCH_DEPTH = 5
    wtm = 1
    fen = "8/8/8/1p4k1/p1p5/P1q5/KP2r3/8"
    p = Position(fen)
    p.w_king_move_count = 5
    p.b_king_move_count = 5
    p.w_rook_a1_move_count = 2
    p.w_rook_h1_move_count = 2
    p.b_rook_a8_move_count = 4
    p.b_rook_h8_move_count = 4
    p.w_rook_a1_location = f1
    p.w_rook_h1_location = f8
    p.b_rook_a8_location = a8
    p.b_rook_h8_location = h8
    print "10. test: draw"
    #print p
    #print "moves are ",p.show_moves(1)
    #p = let_computer_move(p,wtm)
    m =  search_alphabeta(p,wtm)
    #print "m=",m
    if (m == 'a2b1'):
        print "    10.1 draw test: PASSED"
        tests_passed += 1
    else:
        print "    10.1 draw test: FAILED"
        tests_failed += 1

    fen = "8/8/8/4k3/8/4qpK1/8/8"
    #fen = "8/8/8/4k3/8/5p2/6q1/7K"
    p = Position(fen)
    p.w_king_move_count = 5
    p.b_king_move_count = 5
    p.w_rook_a1_move_count = 2
    p.w_rook_h1_move_count = 2
    p.b_rook_a8_move_count = 4
    p.b_rook_h8_move_count = 4
    p.w_rook_a1_location = f1
    p.w_rook_h1_location = f8
    p.b_rook_a8_location = a8
    p.b_rook_h8_location = h8
    print p
    print "moves are ",p.show_moves(1)
    #p = let_computer_move(p,wtm)
    m =  search_alphabeta(p,wtm)
    #print "m=",m
    #print "winner is",p.winner
    if (m == 'g3h2'):
        print "    10.2 draw test: PASSED"
        tests_passed += 1
    else:
        print "    10.2 draw test: FAILED"
        tests_failed += 1


def test_icga ():
    """
    This is some test code for an ICGA Journal article
    """
    # keep a list of position bitbaords used by all tests
    position_list = []
    count = 0
    # for now, we simply use all the Encyclopodia of Chess Middle Games
    for i in open("ECM.epd"):
        line = i.strip()
        fen = line.split()[0]
        # create a position object
        p = Position(fen)

        piece_bb = p.piece_bb

        all_pieces = piece_bb['P']|piece_bb['R']|piece_bb['N']|\
                     piece_bb['B']|piece_bb['Q']|piece_bb['K']|\
                     piece_bb['p']|piece_bb['r']|piece_bb['n']|\
                     piece_bb['b']|piece_bb['q']|piece_bb['k']

        all_pieces90 = 0
        all_pieces45ne = 0
        all_pieces45nw = 0

        # precalculate the rotated boards to be used later
        while(all_pieces):
            piece = lsb(all_pieces)
            all_pieces90 |= rot90[piece]
            all_pieces45ne |= rot45ne[piece]
            all_pieces45nw |= rot45nw[piece]
            all_pieces = clear_lsb(all_pieces)

        p.piece_bb['all_pieces90'] = all_pieces90
        p.piece_bb['all_pieces45ne'] = all_pieces45ne
        p.piece_bb['all_pieces45nw'] = all_pieces45nw

        position_list.append(p)
        count += 1

    start = time.time()
    for i in range(10):
        for p in position_list:
            p.generate_moves(1)
    total1 = time.time() - start
    print "Direct lookup: calls to generate_moves takes %s" % (total1)

    start = time.time()
    for i in range(10):
        for p in position_list:
            p.generate_moves_rot(1)
    total2 = time.time() - start
    print "Rotated Bitboards: calls to generate_moves_rot takes %s" % (total2)

    print "difference = %s" % (100*(total2-total1)/total1)

    # now rerun the tests in the opposite order to see if it makes
    # any difference.
    start = time.time()
    for i in range(10):
        for p in position_list:
            p.generate_moves_rot(1)
    total2 = time.time() - start
    print "Rotated Bitboards: calls to generate_moves_rot takes %s" % (total2)

    start = time.time()
    for i in range(10):
        for p in position_list:
            p.generate_moves(1)
    total1 = time.time() - start
    print "Direct lookup: calls to generate_moves takes %s" % (total1)

    print "difference = %s" % (100*(total2-total1)/total1)

    print "total positions",count


def test ():
    print "\nregression test"
    print "================"
    test_init()
    test_search()
    test_generate_attacks()
    test_repetition()
    test_pinned()
    test_checkmate()
    test_generate_moves()
    test_castling()
    test_check()
    test_checkmated()
    print "==========================================="
    print "total tests PASSED=%s  FAILED=%s" % (tests_passed,tests_failed)
    sys.exit()


##############################################################
# These are constants and arrays used throughout the program #
##############################################################
count = 0
# set the square names equal to their binary values
for i in range(1,9):
    for j in 'hgfedcba':
        name = '%s%s' % (j,i)
        exec(name + "="+str(1L<<count)) # a1 = 1<<7, h1 = 1
        name = name.upper()
        exec(name + "="+str(1L<<count)) # A1 = 1<<7, H1 = 1
        count = count + 1

# this is a static evaluation table used to
# cache the values based on the board position
# i.e. position.hash_index'][0:64] so we ignore
# the side to move, move counts and castle state.
eval_table = {}
EVAL_TABLE_MAX_SIZE = 1000000
eval_table["key_list"] = []
# the transition table keeps track of the best move,
# the depth searched.  These are not currently used.
transition_table = {}
TRANSITION_TABLE_MAX_SIZE = 100000
transition_table["key_list"] = []

START_TIME = 0
SEARCH_DEPTH = 5
STARTING_DEPTH = 3
NULL_MOVE_REDUCTION = 2
CURRENT_VARIATION = []
BEST_VARIATION = []
TIME_LIMIT = 60
#MOBILITY_VALUE = 30
MOBILITY_VALUE = 2
ATTACKING_VALUE = 5
PROTECTING_VALUE = 5
ATTACKED_VALUE = 5
PAWN_VALUE = 100
KNIGHT_VALUE = 322
BISHOP_VALUE = 344
ROOK_VALUE = 561
QUEEN_VALUE = 891
KING_VALUE = 40000
MATE = 60000
INFINITY = 100000
ALL_ONES = (1L<<64) - 1
MOVER_HASH_INDEX = 64
CASTLING_HASH_INDEX = 65
ENPASSANT_HASH_INDEX = 66
HALF_MOVE_HASH_INDEX = 67
FULL_MOVE_HASH_INDEX = 68

PASSED_PAWN_MULT = 20
PASSED_PAWN_KING_SUPPORTED_MULT = 40
PASSED_PAWN_UNBLOCKED_MULT = 8
XBOARD = 0
DEBUG_MOVES = 0

counters = {}
INIT_FEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR"
mover = {0:"black",1:"white"}
bin2alg,bin2index,alg2bin = get_conversions()

try:
    start = time.time()
    bd = open("shatranj-data.bin","r")
    print "...reading startup data"
    knight_moves       = cPickle.load(bd)
    king_moves         = cPickle.load(bd)
    rank               = cPickle.load(bd)
    rank_mask          = cPickle.load(bd)
    rank_attacks       = cPickle.load(bd)
    file               = cPickle.load(bd)
    file_mask          = cPickle.load(bd)
    file_attacks       = cPickle.load(bd)
    diag_mask_ne       = cPickle.load(bd)
    diag_mask_nw       = cPickle.load(bd)
    diag_attacks_ne    = cPickle.load(bd)
    diag_attacks_nw    = cPickle.load(bd)
    above              = cPickle.load(bd)
    below              = cPickle.load(bd)
    left               = cPickle.load(bd)
    right              = cPickle.load(bd)
    white_squares      = cPickle.load(bd)
    black_squares      = cPickle.load(bd)
    piece_square_value = cPickle.load(bd)
    bd.close()
    print "...total time to read data",time.time()-start
except:
    start = time.time()
    print "...generating startup data"
    rank,rank_mask = get_ranks()
    file,file_mask = get_files()
    diag_mask_ne = get_diag_ne()
    diag_mask_nw = get_diag_nw()
    above,below,left,right,white_squares,black_squares = get_direction_masks()
    knight_moves = get_knight_moves()
    king_moves = get_king_moves()
    rank_attacks = get_rank_attacks()
    file_attacks = get_file_attacks()
    diag_attacks_ne = get_diag_attacks_ne()
    diag_attacks_nw = get_diag_attacks_nw()
    piece_square_value = generate_piece_square_values()
    bd = open("shatranj-data.bin","w")
    cPickle.dump(knight_moves,bd)
    cPickle.dump(king_moves,bd)
    cPickle.dump(rank,bd)
    cPickle.dump(rank_mask,bd)
    cPickle.dump(rank_attacks,bd)
    cPickle.dump(file,bd)
    cPickle.dump(file_mask,bd)
    cPickle.dump(file_attacks,bd)
    cPickle.dump(diag_mask_ne,bd)
    cPickle.dump(diag_mask_nw,bd)
    cPickle.dump(diag_attacks_ne,bd)
    cPickle.dump(diag_attacks_nw,bd)
    cPickle.dump(above,bd)
    cPickle.dump(below,bd)
    cPickle.dump(left,bd)
    cPickle.dump(right,bd)
    cPickle.dump(white_squares,bd)
    cPickle.dump(black_squares,bd)
    cPickle.dump(piece_square_value,bd)
    bd.close()
    print "...total time to generate data",time.time()-start

# grab the opening book if we can
try:
    bd = open("shatranj-book.bin")
    book = cPickle.load(bd)
    print "...found opening book shatranj-book.bin with %s positions" % len(book)
except:
    print "Warning: missing opening book shatranj-book.bin"
    book = {}

# these hash tables are only used for testing
rot90,rotminus90 = get_rot90()
rot45ne,rotminus45ne,rot45ne_mask = get_rot45ne()
rot45nw,rotminus45nw,rot45nw_mask = get_rot45nw()
RankAttacks = get_RankAttacks()
FileAttacks = get_FileAttacks()
BishopAttacksNE = get_BishopAttacksNE()
BishopAttacksNW = get_BishopAttacksNW()


######################## main #############################
if __name__ == '__main__':
    try:
        signal.signal(signal.SIGHUP,gotSIGHUP)
        signal.signal(signal.SIGINT,gotSIGINT)
        signal.signal(signal.SIGTERM,gotSIGTERM)
    except:
        pass
    
    if (len(sys.argv) >= 2 and sys.argv[1] == "-t"):
        tests_passed = 0
        tests_failed = 0
        test_number = 0
        test()

    elif (len(sys.argv) >= 2 and sys.argv[1] == "-p"):
        tests_passed = 0
        tests_failed = 0
        profile.run("test_search()")

    elif (len(sys.argv) >= 2 and sys.argv[1] == "-icga"):
        test_icga()

    elif (len(sys.argv) >= 2 and sys.argv[1] == "-xboard"):
        XBOARD = 1
        rc = play()

    else:
        rc = play()
#######################################################################
# The End.
#######################################################################
