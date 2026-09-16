from pathlib import Path
import sys
import math
import itertools
import z3
import pickle
import matplotlib.pyplot as plt
import numpy as np
from csv import DictWriter

NUM_TEAMS = 8
NUM_WEEKS = 12
ADD_EXHIBITION_WEEK = False

EVENT_IDS = []
# NUM_TEAMS = 12
# NUM_WEEKS = 11
# ADD_EXHIBITION_WEEK = True

SEASON_PREFIX = '263F'
DATES = ('09/28/2026',
         '10/05/2026',
         '10/12/2026',
         '10/19/2026',
         '10/26/2026',
         '11/02/2026',
         '11/09/2026',
         '11/16/2026',
         '11/23/2026',
         '11/30/2026',
         '12/07/2026',
         '12/14/2026',)


TIMES = (('18:00:00', '20:00:00'), ('20:30:00', '22:30:00'))
SHEET_NAMES = ('Sheet A', 'Sheet B', 'Sheet C')


class Game():
    def __init__(self, home: int | str, away: int | str, week: int, draw: int, sheet: int, exhibition: bool = False) -> None:
        self._home = home
        self._away = away
        self.week = week
        self.draw = draw
        self.sheet = sheet
        self.exhibition = exhibition

    @property
    def home(self) -> str:
        if isinstance(self._home, int):
            return f'{self._home:02d}'
        return self._home

    @property
    def away(self) -> str:
        if isinstance(self._away, int):
            return f'{self._away:02d}'
        return self._away

    @home.setter
    def home(self, value: int | str):
        self._home = value

    @away.setter
    def away(self, value: int | str):
        self._away = value

    @property
    def teams(self) -> tuple[str, str]:
        return (self.home, self.away)

    def __str__(self):
        return str({'week': self.week,
                    'draw': self.draw,
                    'sheet': self.sheet,
                    'teams': self.teams})


class Schedule():
    TEAMS_PER_GAME = 2

    def __init__(self, num_weeks: int, num_teams: int, num_draws: int = 2, num_sheets: int = 3) -> None:
        self.num_weeks = num_weeks
        self.num_draws = num_draws
        self.num_sheets = num_sheets
        self.num_teams = num_teams

        self.weeks = range(self.num_weeks)
        self.draws = range(self.num_draws)
        self.sheets = range(self.num_sheets)
        self.teams = range(self.num_teams)

        self._games_per_week = min(
            [int(num_teams/2), int(num_draws*num_sheets)])
        self._byes = int(max(0, math.ceil(
            ((num_teams - self._games_per_week*self.TEAMS_PER_GAME)*num_weeks)/(num_teams*1.0))))
        self._games_per_season = num_weeks - self._byes
        self._min_games_against_each_team = math.floor(
            self._games_per_season / (num_teams - 1))
        self._max_games_against_each_team = math.ceil(
            self._games_per_season / (num_teams - 1))
        self._max_late_games = int((self._games_per_week - num_sheets *
                                    (num_draws-1)) * num_weeks / int(num_teams/2)) + 1

        team_bits = int(math.ceil(math.log(num_teams, 2)))
        sheet_bits = int(math.ceil(math.log(num_sheets, 2)))
        draw_bits = int(math.ceil(math.log(num_draws, 2)))
        self._schedule = list()
        for w in self.weeks:
            week = list()
            for g in range(self._games_per_week):
                game = Game(week=w,
                            home=z3.BitVec(f'w{w}_g{g}_home', team_bits),
                            away=z3.BitVec(f'w{w}_g{g}_away', team_bits),
                            sheet=z3.BitVec(f'w{w}_g{g}_sheet', sheet_bits),
                            draw=z3.BitVec(f'w{w}_g{g}_draw', draw_bits))
                week.append(game)
            self._schedule.append(week)

    def games_in_week(self, week: int) -> list[Game]:
        return self._schedule[week]

    def games_in_season(self) -> list[Game]:
        all = list()
        for w in self.weeks:
            all.extend(self.games_in_week(w))
        return all

    def set_bounds(self) -> z3.BoolRef | z3.Probe:
        facts = list()
        # set bounds of values
        for w in self.weeks:
            for g in self.games_in_week(w):
                facts.extend([
                    z3.And(z3.BV2Int(g.home) >= 0,
                           z3.BV2Int(g.home) < self.num_teams),
                    z3.And(z3.BV2Int(g.away) >= 0,
                           z3.BV2Int(g.away) < self.num_teams),
                    z3.And(z3.BV2Int(g.draw) >= 0,
                           z3.BV2Int(g.draw) < self.num_draws),
                    z3.And(z3.BV2Int(g.sheet) >= 0,
                           z3.BV2Int(g.sheet) < self.num_sheets),
                    z3.And(g.home != g.away)
                ])

        # set only 1 game per sheet per draw each week
        for w in self.weeks:
            for d in self.draws:
                for s in self.sheets:
                    combos = [(z3.BV2Int(g.draw) == d,
                               z3.BV2Int(g.sheet) == s)
                              for g in self.games_in_week(w)]
                    slots = [z3.And(*x) for x in combos]
                    facts.append(z3.AtMost(*slots, 1))

        # each team gets same number of games per season
        for t in self.teams:
            combos = [(z3.BV2Int(g.home) == t,
                       z3.BV2Int(g.away) == t)
                      for g in self.games_in_season()]
            slots = [z3.Or(*x) for x in combos]
            facts.append(z3.AtLeast(*slots, self._games_per_season))
            facts.append(z3.AtMost(*slots, self._games_per_season))

        return z3.And(*facts)

    def set_time_sheet_usage(self) -> z3.BoolRef | z3.Probe:
        facts = list()
        for week in self.weeks:
            games = self.games_in_week(week)

            for sheet in self.sheets:
                first_time = [z3.And(z3.BV2Int(game.draw) == 0,
                                     z3.BV2Int(game.sheet) == sheet)
                              for game in games]
                facts.append(z3.AtLeast(*first_time, 1))
                facts.append(z3.AtMost(*first_time, 1))

            for sheet in (0, 1):
                second_time = [z3.And(z3.BV2Int(game.draw) == 1,
                                      z3.BV2Int(game.sheet) == sheet)
                               for game in games]
                facts.append(z3.AtMost(*second_time, 0))

            second_time_sheet_c = [z3.And(z3.BV2Int(game.draw) == 1,
                                          z3.BV2Int(game.sheet) == 2)
                                  for game in games]
            facts.append(z3.AtLeast(*second_time_sheet_c, 1))
            facts.append(z3.AtMost(*second_time_sheet_c, 1))

        return z3.And(*facts)

    def set_symmetry_breaking(self) -> z3.BoolRef | z3.Probe:
        if self.num_teams != 8 or self.num_weeks == 0:
            return z3.BoolVal(True)

        first_week = self.games_in_week(0)
        assignments = ((0, 1, 0, 0),
                       (2, 3, 0, 1),
                       (4, 5, 0, 2),
                       (6, 7, 1, 2))
        return z3.And(*[
            z3.And(z3.BV2Int(game.home) == home,
                   z3.BV2Int(game.away) == away,
                   z3.BV2Int(game.draw) == draw,
                   z3.BV2Int(game.sheet) == sheet)
            for game, (home, away, draw, sheet)
            in zip(first_week, assignments)
        ])

    def set_games_per_team_per_week(self) -> z3.BoolRef | z3.Probe:
        facts = list()
        for w in self.weeks:
            for t in self.teams:
                combos = [(z3.BV2Int(g.home) == t,
                           z3.BV2Int(g.away) == t)
                          for g in self.games_in_week(w)]
                slots = [z3.Or(*x) for x in combos]
                facts.append(
                    z3.And(
                        z3.AtMost(*slots, 1),
                        z3.AtLeast(*slots, 1)
                    )
                )

                # max 1 game per draw for a team
                for d in self.draws:
                    team_combos = [(z3.BV2Int(g.home) == t,
                                    z3.BV2Int(g.away) == t)
                                   for g in self.games_in_week(w)]
                    teams = [z3.Or(*x) for x in team_combos]

                    draws = [z3.BV2Int(g.draw) == d
                             for g in self.games_in_week(w)]
                    slots = [z3.And(*x) for x in zip(teams, draws)]
                    facts.append(z3.AtMost(*slots, 1))

        return z3.And(*facts)

    def each_team_plays_each_other(self):
        min_games = self._min_games_against_each_team
        max_games = self._max_games_against_each_team
        facts = list()
        for t1 in self.teams:
            for t2 in range(t1+1, len(self.teams)):
                teams1 = [(z3.BV2Int(g.home) == t1,
                          z3.BV2Int(g.away) == t1)
                          for g in self.games_in_season()]
                teams2 = [(z3.BV2Int(g.home) == t2,
                          z3.BV2Int(g.away) == t2)
                          for g in self.games_in_season()]

                slots = [
                    z3.And(
                        z3.Or(*x[0]),
                        z3.Or(*x[1]))
                    for x in zip(teams1, teams2)]

                facts.append(z3.AtLeast(*slots, min_games))
                facts.append(z3.AtMost(*slots, max_games))

        return z3.And(*facts)

    def no_repeat_before_all_others(self):
        facts = list()
        for team in self.teams:
            opponents = [opp for opp in self.teams if opp != team]
            for opponent in opponents:
                for week in self.weeks:
                    pair_this_week = [
                        z3.And(
                            z3.Or(z3.BV2Int(g.home) == team,
                                  z3.BV2Int(g.away) == team),
                            z3.Or(z3.BV2Int(g.home) == opponent,
                                  z3.BV2Int(g.away) == opponent))
                        for g in self.games_in_week(week)
                    ]
                    earlier_pair = [
                        z3.And(
                            z3.Or(z3.BV2Int(g.home) == team,
                                  z3.BV2Int(g.away) == team),
                            z3.Or(z3.BV2Int(g.home) == opponent,
                                  z3.BV2Int(g.away) == opponent))
                        for prev_week in self.weeks
                        if prev_week < week
                        for g in self.games_in_week(prev_week)
                    ]
                    other_seen_before = []
                    for other in opponents:
                        if other == opponent:
                            continue
                        seen_other_before = [
                            z3.And(
                                z3.Or(z3.BV2Int(g.home) == team,
                                      z3.BV2Int(g.away) == team),
                                z3.Or(z3.BV2Int(g.home) == other,
                                      z3.BV2Int(g.away) == other))
                            for prev_week in self.weeks
                            if prev_week < week
                            for g in self.games_in_week(prev_week)
                        ]
                        other_seen_before.append(z3.Or(*seen_other_before))

                    facts.append(z3.Implies(
                        z3.And(z3.Or(*pair_this_week), z3.Or(*earlier_pair)),
                        z3.And(*other_seen_before)
                    ))

        return z3.And(*facts)

    def enforce_max_late_draws(self):
        late_draw = self.draws[-1]
        late_games_per_week = self._games_per_week - self.num_sheets * (self.num_draws - 1)
        late_appearances = late_games_per_week * self.num_weeks * self.TEAMS_PER_GAME
        min_late_games = math.floor(late_appearances / self.num_teams)
        max_late_games = math.ceil(late_appearances / self.num_teams)
        facts = list()
        for team in self.teams:
            combos = [z3.And(z3.Or(z3.BV2Int(g.home) == team,
                                   z3.BV2Int(g.away) == team,), z3.BV2Int(g.draw) == late_draw)
                      for g in self.games_in_season()]
            facts.append(z3.AtMost(*combos, max_late_games))
            facts.append(z3.AtLeast(*combos, min_late_games))

        return z3.And(*facts)

    def balance_sheets(self):
        facts = list()
        for team in self.teams:
            for sheet in self.sheets:
                games_per_week = 1 + int(sheet == self.num_sheets - 1)
                average = (games_per_week * self.num_weeks * self.TEAMS_PER_GAME
                           / self.num_teams)
                min_allowed = math.floor(average) - 1
                max_allowed = math.ceil(average) + 1
                combos = [z3.And(z3.Or(z3.BV2Int(g.home) == team,
                                       z3.BV2Int(g.away) == team,), z3.BV2Int(g.sheet) == sheet)
                          for g in self.games_in_season()]
                facts.append(z3.AtLeast(*combos, min_allowed))
                facts.append(z3.AtMost(*combos, max_allowed))

        return z3.And(*facts)

    def max_consecutive_games_on_same_sheet(self, max_consecutive: int):
        pass

    def max_consecutive_games_on_same_draw(self, max_consecutive: int):
        facts = list()
        if max_consecutive >= self._games_per_season:
            max_consecutive = self._games_per_season - 1

        for week in self.weeks[:-max_consecutive-1]:
            for team in self.teams:
                for draw in self.draws:
                    this_week = [z3.And(
                        z3.Or(z3.BV2Int(g.home) == team,
                              z3.BV2Int(g.away) == team),
                        z3.BV2Int(g.draw) == draw)
                        for g in self.games_in_week(week)]
                    next_weeks = list()
                    for nw in range(week + 1, week + max_consecutive):
                        combo = [z3.And(
                            z3.Or(z3.BV2Int(g.home) == team,
                                  z3.BV2Int(g.away) == team),
                            z3.BV2Int(g.draw) == draw)
                            for g in self.games_in_week(nw)]
                        next_weeks.append(z3.Or(*combo))

                    facts.append(z3.Implies(
                        z3.Or(*this_week), z3.Not(z3.And(*next_weeks)), True))
        return z3.And(*facts)


def generate_schedule(num_weeks: int, num_teams: int, num_draws: int = 2, num_sheets: int = 3) -> list[Game]:
    if num_teams % 2 != 0:
        raise ValueError('num_teams must be even for a balanced round-robin schedule')

    teams = list(range(num_teams))
    rotation = teams[:]
    rounds: list[list[tuple[int, int]]] = []
    for _ in range(num_teams - 1):
        pairs: list[tuple[int, int]] = []
        for idx in range(num_teams // 2):
            a = rotation[idx]
            b = rotation[-1 - idx]
            if a == b:
                continue
            pairs.append(tuple(sorted((a, b))))
        rounds.append(sorted(pairs))
        rotation = [rotation[0]] + [rotation[-1]] + rotation[1:-1]

    team_sheet_history: dict[int, list[int]] = {team: [] for team in teams}
    team_late_counts: dict[int, int] = {team: 0 for team in teams}
    team_pair_counts: dict[tuple[int, int], int] = {pair: 0 for pair in [tuple(sorted((a, b))) for a in teams for b in teams if a < b]}
    games: list[Game] = []

    def current_c_streak(team: int) -> int:
        streak = 0
        for sheet in reversed(team_sheet_history[team]):
            if sheet != 2:
                break
            streak += 1
        return streak

    def can_assign_sheet_c(pair: tuple[int, int]) -> bool:
        return all(current_c_streak(team) < 3 for team in pair)

    def schedule_week(week_idx: int) -> bool:
        if week_idx == num_weeks:
            return all(count == 3 for count in team_late_counts.values())

        week_pairs = rounds[week_idx % len(rounds)]
        if week_idx >= len(rounds):
            week_pairs = [week_pairs[(idx + week_idx) % len(week_pairs)] for idx in range(len(week_pairs))]

        late_candidates = sorted(
            [pair for pair in week_pairs
             if team_late_counts[pair[0]] < 3
             and team_late_counts[pair[1]] < 3
             and can_assign_sheet_c(pair)],
            key=lambda pair: (
                current_c_streak(pair[0]) + current_c_streak(pair[1]),
                team_late_counts[pair[0]] + team_late_counts[pair[1]],
                pair[0],
                pair[1],
            )
        )

        for late_pair in late_candidates:
            early_pairs = [pair for pair in week_pairs if pair != late_pair]
            for c_pair in early_pairs:
                if not can_assign_sheet_c(c_pair):
                    continue
                remaining_pairs = [pair for pair in early_pairs if pair != c_pair]
                for sheet_a_pair, sheet_b_pair in ((remaining_pairs[0], remaining_pairs[1]),
                                                    (remaining_pairs[1], remaining_pairs[0])):
                    assignments = ((sheet_a_pair, 0), (sheet_b_pair, 1),
                                   (c_pair, 2), (late_pair, 2))
                    for pair, sheet in assignments:
                        key = tuple(sorted(pair))
                        team_pair_counts[key] += 1
                        draw = 1 if pair == late_pair else 0
                        games.append(Game(home=key[0], away=key[1], week=week_idx,
                                          draw=draw, sheet=sheet))
                        for team in key:
                            team_sheet_history[team].append(sheet)
                            if draw == 1:
                                team_late_counts[team] += 1

                    if schedule_week(week_idx + 1):
                        return True

                    for pair, _ in reversed(assignments):
                        key = tuple(sorted(pair))
                        team_pair_counts[key] -= 1
                        games.pop()
                        for team in key:
                            team_sheet_history[team].pop()
                            if pair == late_pair:
                                team_late_counts[team] -= 1

        return False

    if not schedule_week(0):
        raise RuntimeError('Unable to generate a schedule with a maximum three-game Sheet C streak')

    # exact even late-game target: 3 per team
    if any(v != 3 for v in team_late_counts.values()):
        raise RuntimeError(f'Late draw distribution not even: {team_late_counts}')

    return games


def print_games_per_team(games: list[Game]) -> None:
    teams = get_teams(games)
    weeks = get_weeks(games)
    for team in sorted(teams):
        print(f'Team: {team}')
        for week in sorted(weeks):
            for game in games:
                if week != game.week:
                    continue
                if team not in (game.home, game.away):
                    continue
                opp = game.home if team == game.away else game.away
                print(
                    f'{DATES[game.week]} d:{game.draw}, {SHEET_NAMES[game.sheet]}, opp:{opp}')
        print('')


def get_teams(games: list[Game]) -> list[str]:
    teams = set([x.home for x in games] + [x.away for x in games])
    return sorted(teams)


def get_weeks(games: list[Game]) -> list[int]:
    weeks = set([x.week for x in games])
    return sorted(weeks)


def get_sheets(games: list[Game]) -> list[int]:
    sheets = set([x.sheet for x in games])
    return sorted(sheets)


def get_draws(games: list[Game]) -> list[int]:
    draws = set([x.draw for x in games])
    return sorted(draws)


def count_sheet_appearances(games: list[Game]) -> dict[int, list[int]]:
    teams = get_teams(games)
    sheets = get_sheets(games)
    sheet_counts = {team: [0] * len(sheets) for team in teams}

    for game in games:
        sheet_counts[game.home][game.sheet] += 1
        sheet_counts[game.away][game.sheet] += 1
    return sheet_counts


def count_draw_appearances(games: list[Game]) -> dict[int, list[int]]:
    teams = get_teams(games)
    draws = get_draws(games)
    draw_counts = {team: [0] * len(draws) for team in teams}

    for game in games:
        draw_counts[game.home][game.draw] += 1
        draw_counts[game.away][game.draw] += 1
    return draw_counts


def generate_sheet_graphs(games: list[Game]) -> None:
    # Generate sheet appearance counts
    sheet_counts = count_sheet_appearances(games)
    teams = get_teams(games)
    sheets = get_sheets(games)

    # Plotting the sheet distribution
    fig, ax = plt.subplots(figsize=(12, 8))
    index = np.arange(len(teams))
    bar_width = 0.2

    for i in sheets:
        counts = [sheet_counts[team][i] for team in teams]
        ax.bar(index + i * bar_width, counts,
               bar_width, label=f'Sheet {i + 1}')

    ax.set_xlabel('Teams')
    ax.set_ylabel('Number of Games')
    ax.set_title('Sheet Distribution per Team')
    ax.set_xticks(index + bar_width)
    ax.set_xticklabels(teams, rotation=45)
    ax.legend()

    plt.tight_layout()
    plt.show()


def generate_draw_graphs(games: list[Game]) -> None:
    # Generate slot appearance counts
    slot_counts = count_draw_appearances(games)
    teams = get_teams(games)

    # Plotting the slot distribution
    fig, ax = plt.subplots(figsize=(12, 8))
    index = np.arange(len(teams))
    bar_width = 0.35

    early_counts = [slot_counts[team][0] for team in teams]
    late_counts = [slot_counts[team][1] for team in teams]

    bar1 = ax.bar(index, early_counts, bar_width, label='Early')
    bar2 = ax.bar(index + bar_width, late_counts,
                  bar_width, label='Late')

    ax.set_xlabel('Teams')
    ax.set_ylabel('Number of Games')
    ax.set_title('Game Draw Distribution per Team')
    ax.set_xticks(index + bar_width / 2)
    ax.set_xticklabels(teams, rotation=45)
    ax.legend()

    plt.tight_layout()
    plt.show()


def get_row_data(date: str,
                 start_time: str,
                 end_time: str,
                 location: str,
                 team1: str | None = None,
                 team2: str | None = None,
                 event_id: str | None = None) -> dict[str, str]:
    row = {'Format': 'SportsEngine',
           'Start_Date': date,
           'Start_Time': start_time,
           'End_Date': date,
           'End_Time': end_time,
           'Location': location,
           'Team1_ID': f'{SEASON_PREFIX}{team1}' if team1 is not None else SEASON_PREFIX,
           'Team2_ID': f'{SEASON_PREFIX}{team2}' if team2 is not None else SEASON_PREFIX,
           'Description': '',
           'Location_Url': '',
           'Location_Details': '',
           'All_Day_Event': '0',
           'Event_Type': 'Game',
           'Tags': '',
           'Team1_Is_Home': '1',
           'Team2_Name': '0',
           'Custom_Opponent': 'FALSE'}
    if event_id is not None:
        row['Event_ID'] = event_id

    return row


def write_out_sports_engine_csv(games: list[Game]) -> None:
    rows: list[dict[str, str]] = list()
    # Excel format is %Y-%m-%d %H:%M:%S

    event_idx = 0
    for game in sorted(games, key=lambda x: (x.week, x.draw, x.sheet)):
        row = get_row_data(date=DATES[game.week],
                           start_time=TIMES[game.draw][0],
                           end_time=TIMES[game.draw][1],
                           location=SHEET_NAMES[game.sheet],
                           team1=f'E{game.home}' if game.exhibition else game.home,
                           team2=f'E{game.away}' if game.exhibition else game.away,
                           event_id=str(EVENT_IDS[event_idx]) if EVENT_IDS else None)
        event_idx = event_idx + 1
        rows.append(row)

    with open(f'{SEASON_PREFIX}_League_SE_{NUM_TEAMS}teams.csv', 'w', encoding='ascii', newline='') as fp:
        table = DictWriter(fp, fieldnames=rows[0].keys())
        table.writeheader()
        table.writerows(rows)


def print_bye_weeks(games: list[Game]) -> None:
    weeks = get_weeks(games)
    teams = get_teams(games)
    for week in weeks:
        teams_playing = set()
        for game in games:
            if game.week != week:
                continue
            teams_playing.add(game.home)
            teams_playing.add(game.away)
        not_playing = set(teams) - teams_playing
        if len(not_playing) == 0:
            print(f'{DATES[week]} - No bye week')
        else:
            print(f'{DATES[week]} - Bye teams: {sorted(not_playing)}')


if __name__ == '__main__':
    saved_file = Path(__file__).parent / \
        f'schedule_{NUM_TEAMS}teams_{NUM_WEEKS}weeks.pckl'
    saved_file.unlink(missing_ok=True)
    if saved_file.exists():
        with open(saved_file, 'rb') as fp:
            games: list[Game] = pickle.load(fp)
    else:
        print('Generating Schedule')
        games = generate_schedule(num_weeks=NUM_WEEKS, num_teams=NUM_TEAMS)
        with open(saved_file, 'wb') as fp:
            pickle.dump(games, fp, pickle.HIGHEST_PROTOCOL)

    if ADD_EXHIBITION_WEEK:
        for game in games:
            game.week = game.week + 1

        def get_2_teams_for_exhibition(games: list[Game], sheet: int, draw: int):
            already_playing: set[str] = set()
            for game in games:
                if game.week == 0:
                    already_playing.add(game.away)
                    already_playing.add(game.home)
            teams = set(get_teams(games)) - already_playing
            if len(teams) == 2:
                return tuple(teams)

            sheets = get_sheets(games)
            draws = get_draws(games)

            games_played: dict[str, dict[str, dict[int, int]]] = dict()
            for game in games:
                for team in [game.home, game.away]:
                    # if team not in teams:
                    #     continue
                    if team not in games_played:
                        games_played[team] = {'sheets': {
                            x: 0 for x in sheets}, 'draws': {x: 0 for x in draws}}
                    games_played[team]['sheets'][game.sheet] = games_played[team]['sheets'][game.sheet] + 1
                    games_played[team]['draws'][game.draw] = games_played[team]['draws'][game.draw] + 1

            # get teams if lowest draw equal to draw
            matching_draw: set[str] = set()
            for team in teams:
                draws = games_played[team]['draws']

                if draws[draw] == min(draws.values()):
                    matching_draw.add(team)

            # get teams if lowest draw equal to draw
            matching_sheet: set[str] = set()
            for team in teams:
                sheets = games_played[team]['sheets']

                if sheets[sheet] == min(sheets.values()):
                    matching_sheet.add(team)

            teams = matching_draw & matching_sheet
            matchups = [(x, y) for x in teams for y in teams if x != y]
            matchups.sort(key=lambda x: next(
                game.week for game in games if sorted(x) == sorted(game.teams)), reverse=True)
            return matchups[0]

        draws = get_draws(games)
        sheets = get_sheets(games)
        while len([x for x in games if x.week == 0]) < 6:
            for draw in draws:
                for sheet in sheets:
                    teams = get_2_teams_for_exhibition(games, sheet, draw)
                    if len(teams) < 2:
                        continue

                    games.append(
                        Game(week=0,
                             home=teams[0],
                             away=teams[1],
                             draw=draw,
                             sheet=sheet,
                             exhibition=True))

    for game in games:
        if game.week != 0:
            continue
        for rematch in games:
            if rematch.week == game.week:
                continue
            if sorted(rematch.teams) == sorted(game.teams):
                print(game, 'vs', rematch)

    print_games_per_team(games)
    # generate_sheet_graphs(games)
    # generate_draw_graphs(games)
    write_out_sports_engine_csv(games)
    print_bye_weeks(games)
