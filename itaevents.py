import xml.etree.ElementTree as ET
import random
import uuid
import fetcher
import json
import os
import datetime
import pytz
import requests
from bs4 import BeautifulSoup
import time
import re
from urllib.parse import quote_plus
import urllib.parse
import io
from PIL import Image, ImageDraw, ImageFont
from dotenv import load_dotenv

load_dotenv()

PROXY = os.getenv("PROXY")
GUARCAL = os.getenv("GUARCAL")
DADDY = os.getenv("DADDY")
SKYSTR = os.getenv("SKYSTR")

os.makedirs("logos", exist_ok=True)

# Constants
NUM_CHANNELS = 10000
DADDY_JSON_FILE = "daddyliveSchedule.json"
M3U8_OUTPUT_FILE = "itaevents.m3u8"
LOGO = "https://raw.githubusercontent.com/cribbiox/eventi/refs/heads/main/ddsport.png"

# Add a cache for logos to avoid repeated requests
LOGO_CACHE = {}

# Add a cache for logos loaded from the local file
LOCAL_LOGO_CACHE = []
LOCAL_LOGO_FILE = "guardacalcio_image_links.txt"

EVENT_KEYWORDS = ["italy", "atp", "tennis", "basketball", "formula 1", "formula uno", "f1", "motogp", "moto gp", "volley", "serie a", "serie b", "serie c", "uefa champions", "uefa europa", "conference league", "coppa italia", "premier league", "bundesliga", "la liga", "ligue 1", "ciclismo", "cycling"]

# Dizionario per traduzione termini sportivi inglesi in italiano
SPORT_TRANSLATIONS = {
    "soccer": "calcio",
    "football": "football americano",
    "basketball": "basket",
    "tennis": "tennis",
    "swimming": "nuoto",
    "athletics": "atletica",
    "cycling": "ciclismo",
    "golf": "golf",
    "baseball": "baseball",
    "rugby": "rugby",
    "boxing": "boxe",
    "wrestling": "lotta",
    "volleyball": "pallavolo",
    "hockey": "hockey",
    "horse racing": "ippica",
    "motor sports": "automobilismo",
    "motorsports": "automobilismo",
    "gymnastics": "ginnastica",
    "martial arts": "arti marziali",
    "running": "corsa",
    "ice hockey": "hockey su ghiaccio",
    "field hockey": "hockey su prato",
    "water polo": "pallanuoto",
    "weight lifting": "sollevamento pesi",
    "weightlifting": "sollevamento pesi",
    "skiing": "sci",
    "skating": "pattinaggio",
    "ice skating": "pattinaggio su ghiaccio",
    "fencing": "scherma",
    "archery": "tiro con l'arco",
    "climbing": "arrampicata",
    "rowing": "canottaggio",
    "sailing": "vela",
    "surfing": "surf",
    "fishing": "pesca",
    "dancing": "danza",
    "chess": "scacchi",
    "snooker": "biliardo",
    "billiards": "biliardo",
    "darts": "freccette",
    "badminton": "badminton",
    "cricket": "cricket",
    "aussie rules": "football australiano",
    "australian football": "football australiano",
    "cross country": "corsa campestre",
    "biathlon": "biathlon",
    "waterpolo": "pallanuoto",
    "handball": "pallamano"
}

# Headers for requests
headers = {
    "Accept": "*/*",
    "Accept-Language": "it-IT,it;q=0.9,en-US;q=0.8,en;q=0.7,es;q=0.6,ru;q=0.5",
    "Priority": "u=1, i",
    "sec-ch-ua": '"Not(A:Brand";v="99", "Google Chrome";v="133", "Chromium";v="133"',
    "Sec-Ch-UA-Mobile": "?0",
    "Sec-Ch-UA-Platform": "Windows",
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Site": "same-origin",
    "Sec-Fetch-Storage-Access": "active",
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/133.0.0.0 Safari/537.36",
}

# Remove existing M3U8 file if it exists
if os.path.exists(M3U8_OUTPUT_FILE):
    os.remove(M3U8_OUTPUT_FILE)

def load_local_logos():
    """Loads logo links from the local file into a cache."""
    if not LOCAL_LOGO_CACHE:
        try:
            with open(LOCAL_LOGO_FILE, 'r', encoding='utf-8') as f:
                for line in f:
                    line = line.strip()
                    if line:
                        LOCAL_LOGO_CACHE.append(line)
            print(f"Caricati {len(LOCAL_LOGO_CACHE)} loghi dal file locale: {LOCAL_LOGO_FILE}")
        except FileNotFoundError:
            print(f"File locale dei loghi non trovato: {LOCAL_LOGO_FILE}. Procedo con lo scraping web.")
        except Exception as e:
            print(f"Errore durante il caricamento del file locale dei loghi {LOCAL_LOGO_FILE}: {e}")

def translate_sport_to_italian(sport_key):
    """Traduce i termini sportivi inglesi in italiano"""
    clean_key = re.sub(r'<[^>]+>', '', sport_key).strip().lower()
    if clean_key in SPORT_TRANSLATIONS:
        translated = SPORT_TRANSLATIONS[clean_key]
        return translated.title()
    return clean_group_title(sport_key)

def search_logo_for_event(event_name):
    """
    Cerca un logo per l'evento specificato utilizzando un motore di ricerca
    Restituisce l'URL dell'immagine trovata o None se non trovata
    """
    try:
        # Pulizia nome evento
        clean_event_name = re.sub(r'\s*\(\d{1,2}:\d{2}\)\s*$', '', event_name)
        if ':' in clean_event_name:
            clean_event_name = clean_event_name.split(':', 1)[1].strip()

        # Identificazione squadre
        teams = None
        separators = [" vs ", " VS ", " vs. ", " VS. "]
        for sep in separators:
            if sep in clean_event_name:
                teams = clean_event_name.split(sep)
                break

        if teams and len(teams) == 2:
            team1 = teams[0].strip()
            team2 = teams[1].strip()
            print(f"[🔍] Ricerca logo per Team 1: {team1}")
            logo1_url = search_team_logo(team1)
            print(f"[🔍] Ricerca logo per Team 2: {team2}")
            logo2_url = search_team_logo(team2)

            # Se abbiamo trovato entrambi i loghi, creiamo un'immagine combinata
            if logo1_url and logo2_url:
                try:
                    from os.path import exists, getmtime
                    
                    # Crea la cartella logos se non esiste
                    logos_dir = "logos"
                    os.makedirs(logos_dir, exist_ok=True)

                    # Controllo cache (3 ore) - ESATTAMENTE come in lista.py
                    current_time = time.time()
                    three_hours_in_seconds = 3 * 60 * 60
                    output_filename = f"logos/{team1}_vs_{team2}.png"

                    if exists(output_filename):
                        file_age = current_time - os.path.getmtime(output_filename)
                        if file_age <= three_hours_in_seconds:
                            print(f"[✓] Utilizzo immagine combinata esistente: {output_filename}")
                            # Carica le variabili d'ambiente per GitHub
                            NOMEREPO = os.getenv("NOMEREPO", "").strip()
                            NOMEGITHUB = os.getenv("NOMEGITHUB", "").strip()
                            
                            # Se le variabili GitHub sono disponibili, restituisci l'URL raw di GitHub
                            if NOMEGITHUB and NOMEREPO:
                                github_raw_url = f"https://raw.githubusercontent.com/{NOMEGITHUB}/{NOMEREPO}/main/{output_filename}"
                                print(f"[✓] URL GitHub generato per logo esistente: {github_raw_url}")
                                return github_raw_url
                            else:
                                # Altrimenti restituisci il percorso locale
                                return output_filename

                    # Scarica i loghi - METODO DA lista.py
                    response1 = requests.get(logo1_url, timeout=10)
                    img1 = Image.open(io.BytesIO(response1.content))

                    response2 = requests.get(logo2_url, timeout=10)
                    img2 = Image.open(io.BytesIO(response2.content))

                    # Carica l'immagine VS (assicurati che esista nella directory corrente)
                    vs_path = "vs.png"
                    if exists(vs_path):
                        img_vs = Image.open(vs_path)
                        # Converti l'immagine VS in modalità RGBA se non lo è già
                        if img_vs.mode != 'RGBA':
                            img_vs = img_vs.convert('RGBA')
                    else:
                        # Crea un'immagine di testo "VS" se il file non esiste
                        img_vs = Image.new('RGBA', (100, 100), (255, 255, 255, 0))
                        from PIL import ImageDraw, ImageFont
                        draw = ImageDraw.Draw(img_vs)
                        try:
                            font = ImageFont.truetype("arial.ttf", 40)
                        except:
                            font = ImageFont.load_default()
                        draw.text((30, 30), "VS", fill=(255, 0, 0), font=font)

                    # Ridimensiona le immagini a dimensioni uniformi
                    size = (150, 150)
                    img1 = img1.resize(size)
                    img2 = img2.resize(size)
                    img_vs = img_vs.resize((100, 100))

                    # Assicurati che tutte le immagini siano in modalità RGBA per supportare la trasparenza
                    if img1.mode != 'RGBA':
                        img1 = img1.convert('RGBA')
                    if img2.mode != 'RGBA':
                        img2 = img2.convert('RGBA')

                    # Crea una nuova immagine con spazio per entrambi i loghi e il VS
                    combined_width = 300
                    combined = Image.new('RGBA', (combined_width, 150), (255, 255, 255, 0))

                    # Posiziona le immagini con il VS sovrapposto al centro
                    # Posiziona il primo logo a sinistra
                    combined.paste(img1, (0, 0), img1)
                    # Posiziona il secondo logo a destra
                    combined.paste(img2, (combined_width - 150, 0), img2)
                    # Posiziona il VS al centro, sovrapposto ai due loghi
                    vs_x = (combined_width - 100) // 2

                    # Crea una copia dell'immagine combinata prima di sovrapporre il VS
                    combined_with_vs = combined.copy()
                    combined_with_vs.paste(img_vs, (vs_x, 25), img_vs)
                    # Usa l'immagine con VS sovrapposto
                    combined = combined_with_vs

                    # Salva l'immagine combinata
                    os.makedirs(os.path.dirname(output_filename), exist_ok=True)
                    combined.save(output_filename)
                    print(f"[✓] Immagine combinata creata: {output_filename}")

                    # Carica le variabili d'ambiente per GitHub
                    NOMEREPO = os.getenv("NOMEREPO", "").strip()
                    NOMEGITHUB = os.getenv("NOMEGITHUB", "").strip()

                    # Se le variabili GitHub sono disponibili, restituisci l'URL raw di GitHub
                    if NOMEGITHUB and NOMEREPO:
                        github_raw_url = f"https://raw.githubusercontent.com/{NOMEGITHUB}/{NOMEREPO}/main/{output_filename}"
                        print(f"[✓] URL GitHub generato: {github_raw_url}")
                        return github_raw_url
                    else:
                        # Altrimenti restituisci il percorso locale
                        return output_filename

                except Exception as e:
                    print(f"[!] Errore nella creazione dell'immagine combinata: {e}")
                    # Se fallisce, restituisci solo il primo logo trovato
                    return logo1_url

            # Se non abbiamo trovato entrambi i loghi, restituisci quello che abbiamo
            return logo1_url or logo2_url

        # Ricerca standard per eventi non divisi in squadre
        search_query = urllib.parse.quote(f"{clean_event_name} logo")
        search_url = f"https://www.bing.com/images/search?q={search_query}&qft=+filterui:photo-transparent+filterui:aspect-square"

        # Headers per la ricerca Bing
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/132.0.0.0 Safari/537.36',
            'Accept': 'image/png,image/jpeg,image/svg+xml,image/*,*/*;q=0.8'
        }

        response = requests.get(search_url, headers=headers, timeout=10)
        if response.status_code == 200:
            match = re.search(r'"contentUrl":"(https?://[^"]+\.(?:png|jpg|jpeg|svg))"', response.text)
            return match.group(1) if match else None

        return None

    except Exception as e:
        print(f"[!] Errore nella ricerca del logo: {str(e)}")
        return None


def search_team_logo(team_name):
    """
    Funzione dedicata alla ricerca del logo di una singola squadra
    """
    try:
        search_query = urllib.parse.quote(f"{team_name} logo")
        search_url = f"https://www.bing.com/images/search?q={search_query}&qft=+filterui:photo-transparent+filterui:aspect-square&form=IRFLTR"

        headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/132.0.0.0 Safari/537.36",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8",
            "Accept-Language": "it-IT,it;q=0.9,en-US;q=0.8,en;q=0.7",
            "Cache-Control": "max-age=0",
            "Connection": "keep-alive"
        }

        response = requests.get(search_url, headers=headers, timeout=10)
        if response.status_code == 200:
            patterns = [
                r'murl":"(https?://[^&]+)"',
                r'"murl":"(https?://[^"]+)"',
                r'"contentUrl":"(https?://[^"]+\.(?:png|jpg|jpeg|svg))"',
                r'<img[^>]+src="(https?://[^"]+\.(?:png|jpg|jpeg|svg))[^>]+class="mimg"',
                r'<div[^>]+class="iusc"[^>]+m=\'{"[^"]*":"[^"]*","[^"]*":"(https?://[^"]+)"'
            ]

            for pattern in patterns:
                matches = re.findall(pattern, response.text)
                if matches and len(matches) > 0:
                    for match in matches:
                        if '.png' in match.lower() or '.svg' in match.lower():
                            return match
                    return matches[0]

    except Exception as e:
        print(f"[!] Errore nella ricerca del logo per '{team_name}': {e}")

    return None

def get_dynamic_logo(event_name):
    """
    Cerca immagini dinamiche per eventi
    """
    teams_match = re.search(r':\s*([^:]+?)\s+vs\s+([^:]+?)(?:\s+[-|]|$)', event_name, re.IGNORECASE)
    if not teams_match:
        teams_match = re.search(r'([^:]+?)\s+-\s+([^:]+?)(?:\s+[-|]|$)', event_name, re.IGNORECASE)

    cache_key = None
    team1 = None
    team2 = None
    if teams_match:
        team1 = teams_match.group(1).strip()
        team2 = teams_match.group(2).strip()
        cache_key = f"{team1} vs {team2}"

    if cache_key in LOGO_CACHE:
        print(f"Logo trovato in cache (web) per: {cache_key}")
        return LOGO_CACHE[cache_key]

    load_local_logos()

    if LOCAL_LOGO_CACHE and team1 and team2:
        team1_normalized = team1.lower().replace(" ", "-")
        team2_normalized = team2.lower().replace(" ", "-")

        for logo_url in LOCAL_LOGO_CACHE:
            logo_url_lower = logo_url.lower()
            if team1_normalized in logo_url_lower and team2_normalized in logo_url_lower:
                print(f"Logo trovato nel file locale per: {cache_key} -> {logo_url}")
                if cache_key:
                    LOGO_CACHE[cache_key] = logo_url
                return logo_url
            elif team1_normalized in logo_url_lower or team2_normalized in logo_url_lower:
                print(f"Logo parziale trovato nel file locale per: {cache_key} -> {logo_url}")
                if cache_key:
                    LOGO_CACHE[cache_key] = logo_url
                return logo_url

    is_serie_a_or_other_leagues = any(league in event_name for league in ["Italy - Serie A", "La Liga", "Premier League", "Bundesliga", "Ligue 1"])
    is_serie_b_or_c = any(league in event_name for league in ["Italy - Serie B", "Italy - Serie C"])
    is_uefa_or_coppa = any(league in event_name for league in ["UEFA Champions League", "UEFA Europa League", "Conference League", "Coppa Italia"])

    if not (is_serie_a_or_other_leagues or is_serie_b_or_c or is_uefa_or_coppa):
        print(f"Evento non di lega supportata, usando ricerca Bing: {event_name}")
        logo_result = search_logo_for_event(event_name)
        if logo_result:
            if cache_key:
                LOGO_CACHE[cache_key] = logo_result
            return logo_result
        else:
            if cache_key:
                LOGO_CACHE[cache_key] = LOGO
            return LOGO

    try:
        logo_result = search_logo_for_event(event_name)
        if logo_result:
            if cache_key:
                LOGO_CACHE[cache_key] = logo_result
            return logo_result
    except:
        pass

    return LOGO

def generate_unique_ids(count, seed=42):
    random.seed(seed)
    return [str(uuid.UUID(int=random.getrandbits(128))) for _ in range(count)]

def loadJSON(filepath):
    with open(filepath, 'r', encoding='utf-8') as file:
        return json.load(file)

def get_stream_link(dlhd_id, event_name="", channel_name="", max_retries=3):
    print(f"Getting stream link for channel ID: {dlhd_id} - {event_name} on {channel_name}...")

    if channel_name and "Tennis Stream" in channel_name:
        print(f"Canale Tennis Stream rilevato, utilizzo link fisso per: {event_name}")
        return "https://daddylive.dad/embed/stream-576.php"

    return f"https://daddylive.dad/embed/stream-{dlhd_id}.php"

def clean_group_title(sport_key):
    """Clean the sport key to create a proper group-title"""
    import re
    clean_key = re.sub(r'<[^>]+>', '', sport_key).strip()
    if not clean_key:
        clean_key = sport_key.strip()
    return clean_key.title()

def should_include_channel(channel_name, event_name, sport_key):
    """Check if channel should be included based on keywords"""
    combined_text = (channel_name + " " + event_name + " " + sport_key).lower()
    for keyword in EVENT_KEYWORDS:
        if keyword.lower() in combined_text:
            return True
    return False

def process_events():
    dadjson = loadJSON(DADDY_JSON_FILE)

    total_events = 0
    skipped_events = 0
    filtered_channels = 0
    processed_channels = 0

    excluded_categories = [
        "TV Shows", "Cricket", "Aussie rules", "Snooker", "Baseball",
        "Biathlon", "Cross Country", "Horse Racing", "Ice Hockey",
        "Waterpolo", "Golf", "Darts", "Badminton", "Handball"
    ]

    category_stats = {}
    for day, day_data in dadjson.items():
        try:
            for sport_key, sport_events in day_data.items():
                clean_sport_key = sport_key.replace("<span>", "").replace("</span>", "").strip()
                if clean_sport_key not in category_stats:
                    category_stats[clean_sport_key] = 0
                category_stats[clean_sport_key] += len(sport_events)
        except (KeyError, TypeError):
            pass

    print("\n=== Available Categories ===")
    for category, count in sorted(category_stats.items()):
        excluded = "EXCLUDED" if category in excluded_categories else ""
        print(f"{category}: {count} events {excluded}")
    print("===========================\n")

    unique_ids = generate_unique_ids(NUM_CHANNELS)

    with open(M3U8_OUTPUT_FILE, 'w', encoding='utf-8') as file:
        file.write('#EXTM3U\n')

        for day, day_data in dadjson.items():
            try:
                for sport_key, sport_events in day_data.items():
                    clean_sport_key = sport_key.replace("<span>", "").replace("</span>", "").strip()
                    total_events += len(sport_events)

                    if clean_sport_key in excluded_categories:
                        skipped_events += len(sport_events)
                        continue

                    for game in sport_events:
                        for channel in game.get("channels", []):
                            try:
                                clean_day = day.replace(" - Schedule Time UK GMT", "")
                                clean_day = clean_day.replace("st ", " ").replace("nd ", " ").replace("rd ", " ").replace("th ", " ")
                                import re
                                clean_day = re.sub(r'(\d+)(st|nd|rd|th)', r'\1', clean_day)

                                print(f"Original day: '{day}'")
                                print(f"Clean day after processing: '{clean_day}'")

                                day_parts = clean_day.split()
                                print(f"Day parts: {day_parts}")

                                day_num = None
                                month_name = None
                                year = None

                                if len(day_parts) >= 4:
                                    weekday = day_parts[0]

                                    if any(c.isalpha() for c in day_parts[1]):
                                        month_name = day_parts[1]
                                        day_num = day_parts[2]
                                    elif any(c.isalpha() for c in day_parts[2]):
                                        day_num = day_parts[1]
                                        month_name = day_parts[2]
                                    else:
                                        day_num = day_parts[1]
                                        month_name = day_parts[2]

                                    year = day_parts[3]
                                    print(f"Parsed date components: weekday={weekday}, day={day_num}, month={month_name}, year={year}")

                                elif len(day_parts) == 3:
                                    if day_parts[0].lower() in ["monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"]:
                                        day_num = day_parts[1]
                                        rome_tz = pytz.timezone('Europe/Rome')
                                        current_month = datetime.datetime.now(rome_tz).strftime('%B')
                                        month_name = current_month
                                        year = day_parts[2]
                                    else:
                                        day_num = day_parts[0]
                                        month_name = day_parts[1]
                                        year = day_parts[2]
                                else:
                                    rome_tz = pytz.timezone('Europe/Rome')
                                    now = datetime.datetime.now(rome_tz)
                                    day_num = now.strftime('%d')
                                    month_name = now.strftime('%B')
                                    year = now.strftime('%Y')
                                    print(f"Using current Rome date for: {clean_day}")

                                if day_num:
                                    day_num_digits = re.sub(r'[^0-9]', '', str(day_num))
                                    if day_num_digits:
                                        day_num = day_num_digits
                                    else:
                                        rome_tz = pytz.timezone('Europe/Rome')
                                        day_num = datetime.datetime.now(rome_tz).strftime('%d')
                                        print(f"Warning: Invalid day number '{day_num}', using current day: {day_num}")
                                else:
                                    rome_tz = pytz.timezone('Europe/Rome')
                                    day_num = datetime.datetime.now(rome_tz).strftime('%d')
                                    print(f"Warning: Missing day number, using current day: {day_num}")

                                time_str = game.get("time", "00:00")

                                time_parts = time_str.split(":")
                                if len(time_parts) == 2:
                                    hour = int(time_parts[0])
                                    minute = time_parts[1]

                                    hour_cet = (hour + 2) % 24
                                    hour_cet_str = f"{hour_cet:02d}"
                                    time_str_cet = f"{hour_cet_str}:{minute}"
                                else:
                                    time_str_cet = time_str

                                month_map = {
                                    "January": "01", "February": "02", "March": "03", "April": "04",
                                    "May": "05", "June": "06", "July": "07", "August": "08",
                                    "September": "09", "October": "10", "November": "11", "December": "12"
                                }

                                if not month_name or month_name not in month_map:
                                    print(f"Warning: Invalid month name '{month_name}', using current month")
                                    rome_tz = pytz.timezone('Europe/Rome')
                                    current_month = datetime.datetime.now(rome_tz).strftime('%B')
                                    month_name = current_month

                                month_num = month_map.get(month_name, "01")

                                if len(str(day_num)) == 1:
                                    day_num = f"0{day_num}"

                                year_short = str(year)[-2:]
                                formatted_date_time = f"{day_num}/{month_num}/{year_short} - {time_str_cet}"

                                try:
                                    if not day_num or day_num == "":
                                        rome_tz = pytz.timezone('Europe/Rome')
                                        day_num = datetime.datetime.now(rome_tz).strftime('%d')
                                        print(f"Using current day as fallback: {day_num}")

                                    if not month_num or month_num == "":
                                        month_num = "01"
                                        print(f"Using January as fallback month")

                                    if not year or year == "":
                                        rome_tz = pytz.timezone('Europe/Rome')
                                        year = datetime.datetime.now(rome_tz).strftime('%Y')
                                        print(f"Using current year as fallback: {year}")

                                    if not time_str or time_str == "":
                                        time_str = "00:00"
                                        print(f"Using 00:00 as fallback time")

                                    try:
                                        day_int = int(day_num)
                                        if day_int < 1 or day_int > 31:
                                            day_num = "01"
                                            print(f"Day number out of range, using 01 as fallback")
                                    except ValueError:
                                        day_num = "01"
                                        print(f"Invalid day number format, using 01 as fallback")

                                    if len(str(day_num)) == 1:
                                        day_num = f"0{day_num}"

                                    date_str = f"{year}-{month_num}-{day_num} {time_str}:00"
                                    print(f"Attempting to parse date: '{date_str}'")

                                    start_date_utc = datetime.datetime.strptime(date_str, "%Y-%m-%d %H:%M:%S")

                                    amsterdam_timezone = pytz.timezone("Europe/Amsterdam")
                                    start_date_amsterdam = start_date_utc.replace(tzinfo=pytz.UTC).astimezone(amsterdam_timezone)

                                    mStartTime = start_date_amsterdam.strftime("%Y%m%d%H%M%S")
                                    mStopTime = (start_date_amsterdam + datetime.timedelta(days=2)).strftime("%Y%m%d%H%M%S")

                                except ValueError as e:
                                    error_msg = str(e)
                                    if 'date_str' not in locals():
                                        date_str = f"Error with: {year}-{month_num}-{day_num} {time_str}:00"

                                    print(f"Date parsing error: {error_msg} for date string '{date_str}'")

                                    amsterdam_timezone = pytz.timezone("Europe/Amsterdam")
                                    now = datetime.datetime.now(amsterdam_timezone)
                                    mStartTime = now.strftime("%Y%m%d%H%M%S")
                                    mStopTime = (now + datetime.timedelta(days=2)).strftime("%Y%m%d%H%M%S")

                                if isinstance(channel, dict) and "channel_name" in channel:
                                    channelName = formatted_date_time + " " + channel["channel_name"]
                                else:
                                    channelName = formatted_date_time + " " + str(channel)

                                event_name = game["event"].split(":")[0].strip() if ":" in game["event"] else game["event"].strip()
                                event_details = game["event"]

                            except Exception as e:
                                print(f"Error processing date '{day}': {e}")
                                print(f"Game time: {game.get('time', 'No time found')}")
                                continue

                            if should_include_channel(channelName, event_name, sport_key):
                                try:
                                    if isinstance(channel, dict) and "channel_id" in channel:
                                        channelID = f"{channel['channel_id']}"
                                    else:
                                        channelID = str(uuid.uuid4())

                                    if isinstance(channel, dict) and "channel_name" in channel:
                                        channel_name_str = channel["channel_name"]
                                    else:
                                        channel_name_str = str(channel)

                                    stream_url_dynamic = get_stream_link(channelID, event_details, channel_name_str)

                                    if stream_url_dynamic:
                                        if isinstance(channel, dict) and "channel_name" in channel:
                                            channel_name_str = channel["channel_name"]
                                        else:
                                            channel_name_str = str(channel)

                                        time_only = time_str_cet if time_str_cet else "00:00"
                                        tvg_name = f"{time_only} {event_details} - {day_num}/{month_num}/{year_short}"

                                        event_logo = get_dynamic_logo(game["event"])
                                        italian_sport_key = translate_sport_to_italian(clean_sport_key)

                                        file.write(f'#EXTINF:-1 tvg-id="{event_name} - {event_details.split(":", 1)[1].strip() if ":" in event_details else event_details}" tvg-name="{tvg_name}" tvg-logo="{event_logo}" group-title="{italian_sport_key}", {channel_name_str}\n')
                                        file.write(f"{PROXY}{stream_url_dynamic}\n\n")

                                        processed_channels += 1
                                        filtered_channels += 1
                                    else:
                                        print(f"Failed to get stream URL for channel ID: {channelID}")

                                except KeyError as e:
                                    print(f"KeyError: {e} - Key may not exist in JSON structure")
                                    continue
                                except Exception as e:
                                    print(f"Errore generale durante l'elaborazione del canale: {e}")
                                    continue
                            else:
                                print(f"Skipping channel (no keyword match): {clean_group_title(sport_key)} - {event_details} - {channelName}")

            except (KeyError, TypeError) as e:
                print(f"Error processing day data: {e}")
                continue

    print(f"\n=== Processing Summary ===")
    print(f"Total events found: {total_events}")
    print(f"Events skipped due to category filters: {skipped_events}")
    print(f"Channels included due to keyword match: {filtered_channels}")
    print(f"Channels successfully processed: {processed_channels}")
    print(f"Keywords used for filtering: {EVENT_KEYWORDS}")
    print(f"===========================\n")

    return processed_channels

def main():
    total_processed_channels = process_events()

    if total_processed_channels == 0:
        print("No valid channels found matching the keywords.")
    else:
        print(f"M3U8 generated with {total_processed_channels} channels filtered by keywords.")

if __name__ == "__main__":
    main()
