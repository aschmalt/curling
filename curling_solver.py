from typing import Iterable
# from pysmt.shortcuts import (
#     z3.Bool, Int, GE, LT, TRUE, FALSE,  is_sat, get_model, NotEquals, Equals,
#     ExactlyOne)
import z3
from pysmt.typing import INT

TEAMS_PER_GAME = 2


def AllDifferent(args):
    """ Encodes the 'all-different' constraint using two possible
    encodings.

    AllDifferent(x, y, z) := (x != y) & (x != z) & (y != z)
    """
    res = []
    for i, a in enumerate(args):
        for b in args[i+1:]:
            res.append(z3.Not(z3.is_eq(a, b)))
    return z3.And(res)


def game_in_draw(game: int, draw: int) -> z3.BoolRef:
    return z3.Bool(f'{game}_game_in_draw_{draw}')


def game_on_sheet(game: int, sheet: int) -> z3.BoolRef:
    return z3.Bool(f'{game}_game_on_sheet_{sheet}')


def game_in_week(game: int, week: int) -> z3.BoolRef:
    return z3.Bool(f'{game}_game_in_week_{week}')


def team_in_game(game: int, team: int) -> z3.BoolRef:
    return z3.Bool(f'{team}_team_in_game_{game}')


def teams_per_game(teams: Iterable, games: Iterable):
    facts = True
    for g in games:
        opponents = [team_in_game(team=t, game=g) for t in teams]
        facts = z3.And(facts,
                       z3.AtLeast(*opponents, TEAMS_PER_GAME),
                       z3.AtMost(*opponents, TEAMS_PER_GAME))
    return facts


def teams_per_week(games: Iterable, teams: Iterable, weeks: Iterable):
    facts = True
    for w in weeks:
        for t in teams:
            values = [z3.And(game_in_week(game=g, week=w),
                             team_in_game(game=g, team=t)) for g in games]
            facts = z3.And(facts, z3.AtMost(*values, 1))
    return facts


def games_per_week(weeks: Iterable, games: Iterable, games_per_week: int):
    facts = True
    for w in weeks:
        values = [game_in_week(game=g, week=w) for g in games]
        facts = z3.And(facts,
                       z3.AtMost(*values, games_per_week),
                       z3.AtLeast(*values, games_per_week),
                       )
    return facts


def sheets_once_per_draw(weeks: Iterable, sheets: Iterable, draws: Iterable, games: Iterable):
    facts = True
    for w in weeks:
        for d in draws:
            for s in sheets:
                values = [z3.And(game_in_week(g, w),
                                 game_in_draw(g, d),
                                 game_on_sheet(g, s)) for g in games]
                facts = z3.And(facts, z3.AtMost(*values, 1))
    return facts


def games_per_draw(weeks: Iterable, sheets: Iterable, draws: Iterable, games: Iterable):
    facts = True
    for w in weeks:
        for d in draws:
            values = [z3.And(game_in_week(g, w),
                             game_in_draw(g, d)) for g in games]
            facts = z3.And(facts, z3.AtMost(*values, len(list(sheets))))
    return facts

# def sheet_in_draw(sheet: int, draw: int) -> Union[z3.Bool, FALSE]:
#     assert sheet in Sheets
#     if draw in Draws:
#         return z3.Bool(f'{sheet}_sheet_in_draw_{draw}')
#     return FALSE()


# def sheets_per_draw(num_sheets: int, num_draws: int):
#     for week in Weeks:
#         for draw in Draws:
#             And(game_in_week(1, week), game_in_draw(1, draw))


if __name__ == '__main__':
    num_draws = 2
    num_sheets = 3
    num_weeks = 2
    num_teams = 12

    Weeks = range(num_weeks)
    Draws = range(num_draws)
    Sheets = range(num_sheets)
    Teams = range(num_teams)

    import math
    GAMES_PER_WEEK = min([int(num_teams/2), int(num_draws*num_sheets)])
    BYES = int(max(0, math.ceil(
        ((num_teams - GAMES_PER_WEEK*TEAMS_PER_GAME)*num_weeks)/(num_teams*1.0))))
    GAMES_PER_SEASON = num_weeks - BYES
    MIN_GAMES_AGAINST_EACH_TEAM = math.floor(
        GAMES_PER_SEASON / (num_teams - 1))
    MAX_GAMES_AGAINST_EACH_TEAM = math.ceil(GAMES_PER_SEASON / (num_teams - 1))
    MAX_LATE_GAMES = int((GAMES_PER_WEEK - num_sheets *
                         (num_draws-1)) * num_weeks / int(num_teams/2)) + 1

    Games = range(int(GAMES_PER_SEASON * num_teams / TEAMS_PER_GAME))

    s = z3.Solver()
    facts = z3.And(teams_per_game(teams=Teams,
                                  games=Games),
                   teams_per_week(weeks=Weeks,
                                  teams=Teams,
                                  games=Games),
                   games_per_week(weeks=Weeks,
                                  games=Games,
                                  games_per_week=GAMES_PER_WEEK),
                   games_per_draw(weeks=Weeks,
                                  sheets=Sheets,
                                  draws=Draws,
                                  games=Games),
                   sheets_once_per_draw(sheets=Sheets,
                                        weeks=Weeks,
                                        games=Games,
                                        draws=Draws))
    s.add(facts)
    assert s.check() == z3.sat

    m = s.model()
    for w in Weeks:
        week_games = [g for g in Games if z3.is_true(m.evaluate(
            game_in_week(game=g, week=w)))]

        for d in Draws:
            draw_games = [g for g in week_games if z3.is_true(m.evaluate(
                game_in_draw(game=g, draw=d)))]

            for s in Sheets:
                sheet_games = [g for g in draw_games if z3.is_true(m.evaluate(
                    game_on_sheet(game=g, sheet=s)))]

                for g in sheet_games:
                    teams = [x for x in Teams if z3.is_true(m.evaluate(
                        team_in_game(team=x, game=g)))]
            # for t in Teams
            #     elem = te:am_in_game(team=t, game=game)
            #     print(f'T{t} e:{elem}')
                    print(f'{g} W:{w} D:{d} S:{s} T: {teams}')

    import sys
    sys.exit()
    model = get_model(facts)

    if model:
        print(model)

    else:
        print("No solution found")
