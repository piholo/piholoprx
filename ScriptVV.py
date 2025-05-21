#!/usr/bin/env python3
import requests
import json
import logging
import sys
import re
import os

def get_auth_signature():
    headers = {
        "user-agent": "okhttp/4.11.0",
        "accept": "application/json",
        "content-type": "application/json; charset=utf-8",
        "content-length": "1106",
        "accept-encoding": "gzip"
    }

    data = {
        "token": "8Us2TfjeOFrzqFFTEjL3E5KfdAWGa5PV3wQe60uK4BmzlkJRMYFu0ufaM_eeDXKS2U04XUuhbDTgGRJrJARUwzDyCcRToXhW5AcDekfFMfwNUjuieeQ1uzeDB9YWyBL2cn5Al3L3gTnF8Vk1t7rPwkBob0swvxA",
        "reason": "player.enter",
        "locale": "de",
        "theme": "dark",
        "metadata": {
            "device": {
                "type": "Handset",
                "brand": "google",
                "model": "Nexus 5",
                "name": "21081111RG",
                "uniqueId": "d10e5d99ab665233"
            },
            "os": {
                "name": "android",
                "version": "7.1.2",
                "abis": ["arm64-v8a", "armeabi-v7a", "armeabi"],
                "host": "android"
            },
            "app": {
                "platform": "android",
                "version": "3.0.2",
                "buildId": "288045000",
                "engine": "jsc",
                "signatures": ["09f4e07040149486e541a1cb34000b6e12527265252fa2178dfe2bd1af6b815a"],
                "installer": "com.android.secex"
            },
            "version": {
                "package": "tv.vavoo.app",
                "binary": "3.0.2",
                "js": "3.1.4"
            }
        },
        "appFocusTime": 27229,
        "playerActive": True,
        "playDuration": 0,
        "devMode": False,
        "hasAddon": True,
        "castConnected": False,
        "package": "tv.vavoo.app",
        "version": "3.1.4",
        "process": "app",
        "firstAppStart": 1728674705639,
        "lastAppStart": 1728674705639,
        "ipLocation": "",
        "adblockEnabled": True,
        "proxy": {
            "supported": ["ss"],
            "engine": "ss",
            "enabled": False,
            "autoServer": True,
            "id": "ca-bhs"
        },
        "iap": {
            "supported": False
        }
    }

    try:
        response = requests.post("https://www.vavoo.tv/api/app/ping", json=data, headers=headers)
        response.raise_for_status()
        res_json = response.json()
        return res_json.get("addonSig")
    except Exception as e:
        print(f"Errore durante il recupero della firma: {e}")
        return None

def setup_logging():
    logging.basicConfig(filename="excluded_channels.log", level=logging.INFO, format="%(asctime)s - %(message)s")

# Categorie di contenuti
CATEGORY_KEYWORDS = {
    "Sport": ["sport", "dazn", "eurosport", "sky sport", "rai sport", "sport", "dazn", "tennis", "moto", "f1", "golf", "sportitalia", "sport italia", "solo calcio", "solocalcio"],
    "Film": ["primafila", "cinema", "movie", "film", "serie", "hbo", "fox"],
    "Notizie": ["news", "tg", "rai news", "sky tg", "tgcom"],
    "Intrattenimento": ["rai", "mediaset", "italia", "focus", "real time"],
    "Bambini": ["cartoon", "boing", "nick", "disney", "baby", "boing", "cartoon", "k2", "discovery k2", "nick", "super", "frisbee"],
    "Documentari": ["discovery", "geo", "history", "nat geo", "nature", "arte", "documentary"],
    "Musica": ["mtv", "vh1", "radio", "music"]
}

# Categorie di provider
CATEGORY_KEYWORDS2 = {
    "Sky": ["sky cin", "tv 8", "fox", "comedy central", "animal planet", "nat geo", "tv8", "sky atl", "sky uno", "sky prima", "sky serie", "sky arte", "sky docum", "sky natu", "cielo", "history", "sky tg"],
    "Rai Tv": ["rai"],
    "Mediaset": ["mediaset", "canale 5", "rete 4", "italia", "focus", "tg com 24", "tgcom 24", "premium crime", "iris", "mediaset iris", "cine 34", "27 twenty seven", "27 twentyseven"],
    "Discovery": ["discovery", "real time", "investigation", "top crime", "wwe", "hgtv", "nove", "dmax", "food network", "warner tv"],
    "Rakuten": ["rakuten"]
}

# Filtri per includere solo canali specifici
CHANNEL_FILTERS = [
    "sky", "fox", "rai", "cine34", "real time", "crime+ investigation", "top crime", "wwe", "tennis", "k2",
    "inter", "rsi", "la 7", "la7", "la 7d", "la7d", "27 twentyseven", "premium crime", "comedy central", "super!",
    "animal planet", "hgtv", "catfish", "rakuten", "nickelodeon", "cartoonito", "nick jr",
    "history", "nat geo", "tv8", "canale 5", "italia", "mediaset", "rete 4", "focus", "iris", "discovery", "dazn",
    "cine 34", "la 5", "giallo", "dmax", "cielo", "eurosport", "disney+", "food", "tv 8", "mototrend", "boing",
    "frisbee", "deejay tv", "cartoon network", "tg com 24", "warner tv", "boing plus", "27 twenty seven", "tgcom 24",
    "sky uno"
]

# Filtri per escludere canali specifici
CHANNEL_REMOVE = [
    "maria+vision", "telepace", "uninettuno", "lombardia", "cusano", "fm italia", "juwelo", "kiss kiss", "qvc", "rete tv",
    "italia 3", "fishing", "inter tv", "avengers"
]

# Mappatura dei loghi per canali specifici
CHANNEL_LOGOS = {
    "sky uno": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-uno-it.png",
    "rai 1": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-1-it.png",
    "rai 2": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-2-it.png",
    "rai 3": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-3-it.png",
    "eurosport 1": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/spain/eurosport-1-es.png",
    "eurosport 2": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/spain/eurosport-2-es.png",
    "italia 1": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/italia1-it.png",
    "la 7": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/la7-it.png",
    "la 7 d": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/la7d-it.png",
    "rai sport+": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-sport-it.png",
    "rai sport [live during events only]": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-sport-it.png",
    "rai premium": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-premium-it.png",
    "sky sport golf": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-golf-it.png",
    "sky sport moto gp": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-motogp-it.png",
    "sky sport tennis": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-tennis-it.png",
    "sky sport f1": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-f1-it.png",
    "sky sport football": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-football-it.png",
    "sky sport football [live during events only]": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-football-it.png",
    "sky sport uno": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-uno-it.png",
    "sky sport arena": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-arena-it.png",
    "sky cinema collection": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-collection-it.png",
    "sky cinema uno": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-uno-it.png",
    "sky cinema action": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-action-it.png",
    "sky cinema action (backup)": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-action-it.png",
    "sky cinema comedy": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-comedy-it.png",
    "sky cinema uno +24": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-uno-plus24-it.png",
    "sky cinema romance": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-romance-it.png",
    "sky cinema family": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-family-it.png",
    "sky cinema due +24": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-due-plus24-it.png",
    "sky cinema drama": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-drama-it.png",
    "sky cinema suspense": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-suspense-it.png",
    "sky sport 24": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-24-it.png",
    "sky sport 24 [live during events only]": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-24-it.png",
    "sky sport calcio": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-calcio-it.png",
    "sky calcio 1": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/germany/sky-select-1-alt-de.png",
    "sky calcio 2": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/germany/sky-select-2-alt-de.png",
    "sky calcio 3": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/germany/sky-select-3-alt-de.png",
    "sky calcio 4": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/germany/sky-select-4-alt-de.png",
    "sky calcio 5": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/germany/sky-select-5-alt-de.png",
    "sky calcio 6": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/germany/sky-select-6-alt-de.png",
    "sky calcio 7": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/germany/sky-select-7-alt-de.png",
    "sky serie": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-serie-it.png",
    "crime+ investigation": "https://upload.wikimedia.org/wikipedia/commons/4/4d/Crime_%2B_Investigation_Logo_10.2019.svg",
    "20 mediaset": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/20-it.png",
    "mediaset 20": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/20-it.png",
    "27 twenty seven": "https://upload.wikimedia.org/wikipedia/commons/thumb/2/26/Twentyseven_logo.svg/260px-Twentyseven_logo.svg.png",
    "27 twentyseven": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/20-it.png",
    "canale 5": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/canale5-it.png",
    "cine 34 mediaset": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/cine34-it.png",
    "cine 34": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/cine34-it.png",
    "discovery focus": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/focus-it.png",
    "focus": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/focus-it.png",
    "italia 2": "https://upload.wikimedia.org/wikipedia/it/thumb/c/c5/Logo_Italia2.svg/520px-Logo_Italia2.svg.png",
    "mediaset italia 2": "https://upload.wikimedia.org/wikipedia/it/thumb/c/c5/Logo_Italia2.svg/520px-Logo_Italia2.svg.png",
    "mediaset italia": "https://www.italiasera.it/wp-content/uploads/2019/06/Mediaset-640x366.png",
    "mediaset extra": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/mediaset-extra-it.png",
    "mediaset 1": "https://play-lh.googleusercontent.com/2-Cl0plYUCxk8bnbeavm4ZOJ_S4Xuwmql_N3_E4OJyf7XK_YUvdNOWgzn8KD-Bur8w0",
    "mediaset infinity+ 1": "https://play-lh.googleusercontent.com/2-Cl0plYUCxk8bnbeavm4ZOJ_S4Xuwmql_N3_E4OJyf7XK_YUvdNOWgzn8KD-Bur8w0",
    "mediaset infinity+ 2": "https://play-lh.googleusercontent.com/2-Cl0plYUCxk8bnbeavm4ZOJ_S4Xuwmql_N3_E4OJyf7XK_YUvdNOWgzn8KD-Bur8w0",
    "mediaset infinity+ 5": "https://play-lh.googleusercontent.com/2-Cl0plYUCxk8bnbeavm4ZOJ_S4Xuwmql_N3_E4OJyf7XK_YUvdNOWgzn8KD-Bur8w0",
    "mediaset iris": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/iris-it.png",
    "iris": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/iris-it.png",
    "rete 4": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rete4-it.png",
    "sport italia (backup)": "https://play-lh.googleusercontent.com/0IcWROAOpuEcMf2qbOBNQYhrAPUuSmw-zv0f867kUxKSwSTD_chyCDuBP2PScIyWI9k",
    "sport italia": "https://play-lh.googleusercontent.com/0IcWROAOpuEcMf2qbOBNQYhrAPUuSmw-zv0f867kUxKSwSTD_chyCDuBP2PScIyWI9k",
    "sportitalia plus": "https://www.capitaladv.eu/wp-content/uploads/2020/07/LOGO-SPORTITALIA-PLUS-HD_2-1.png",
    "sport italia solo calcio [live during events only]": "https://upload.wikimedia.org/wikipedia/commons/thumb/3/36/SI_Solo_Calcio_logo_%282019%29.svg/1200px-SI_Solo_Calcio_logo_%282019%29.svg.png",
    "sportitalia solocalcio": "https://upload.wikimedia.org/wikipedia/commons/thumb/3/36/SI_Solo_Calcio_logo_%282019%29.svg/1200px-SI_Solo_Calcio_logo_%282019%29.svg.png",
    "dazn": "https://upload.wikimedia.org/wikipedia/commons/thumb/7/71/DAZN_logo.svg/1024px-DAZN_logo.svg.png",
    "dazn 1": "https://upload.wikimedia.org/wikipedia/commons/4/49/DAZN_1.svg",
    "dazn 2": "https://upload.wikimedia.org/wikipedia/commons/7/76/DAZN_2.svg",
    "zona dazn": "https://www.digital-news.it/img/palinsesti/2023/12/1701423631-zona-dazn.webp",
    "motortrend": "https://upload.wikimedia.org/wikipedia/commons/thumb/3/39/Motor_Trend_logo.svg/2560px-Motor_Trend_logo.svg.png",
    "sky sport max": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-max-it.png",
    "sky sport nba": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-nba-it.png",
    "sky sport serie a": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-serie-a-it.png",
    "sky sports f1": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-f1-it.png",
    "sky super tennis": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-sport-tennis-it.png",
    "tennis channel": "https://images.tennis.com/image/upload/t_16-9_768/v1620828532/tenniscom-prd/assets/Fallback/Tennis_Fallback_v6_f5tjzv.jpg",
    "super tennis": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/super-tennis-it.png",
    "tv 8": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/tv8-it.png",
    "sky primafila 1": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 2": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 3": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 4": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 5": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 6": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 7": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 8": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 9": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 10": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 11": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 12": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 13": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 14": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 15": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 16": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 17": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky primafila 18": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-primafila-it.png",
    "sky cinema due": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-cinema-due-it.png",
    "sky atlantic": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-atlantic-it.png",
    "nat geo": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/national-geographic-it.png",
    "discovery nove": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/nove-it.png",
    "discovery channel": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/discovery-channel-it.png",
    "real time": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/real-time-it.png",
    "rai 5": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-5-it.png",
    "rai gulp": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-gulp-it.png",
    "rai italia": "https://upload.wikimedia.org/wikipedia/commons/thumb/8/8a/Rai_Italia_-_Logo_2017.svg/1024px-Rai_Italia_-_Logo_2017.svg.png",
    "rai movie": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-movie-it.png",
    "rai news 24": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-news-24-it.png",
    "rai scuola": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-scuola-it.png",
    "rai storia": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-storia-it.png",
    "rai yoyo": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-yoyo-it.png",
    "rai 4": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/rai-4-it.png",
    "rai 4k": "https://upload.wikimedia.org/wikipedia/commons/thumb/b/bc/Rai_4K_-_Logo_2017.svg/1200px-Rai_4K_-_Logo_2017.svg.png",
    "hgtv": "https://d204lf4nuskf6u.cloudfront.net/italy-images/c2cbeaabb81be73e81c7f4291cf798e3.png?k=2nWZhtOSUQdq2s2ItEDH5%2BQEPdq1khUY8YJSK0%2BNV90dhkyaUQQ82V1zGPD7O5%2BS",
    "top crime": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/top-crime-it.png",
    "cielo": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/cielo-it.png",
    "dmax": "https://cdn.cookielaw.org/logos/50417659-aa29-4f7f-b59d-f6e887deed53/a32be519-de41-40f4-abed-d2934ba6751b/9a44af24-5ca6-4098-aa95-594755bd7b2d/dmax_logo.png",
    "food network": "https://upload.wikimedia.org/wikipedia/commons/f/f4/Food_Network_-_Logo_2016.png",
    "giallo": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/giallo-it.png",
    "history": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/history-channel-it.png",
    "la 5": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/la5-it.png",
    "la 7 d": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/la7d-it.png",
    "sky arte": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-arte-it.png",
    "sky documentaries": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-documentaries-it.png",
    "sky nature": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/sky-nature-it.png",
    "warner tv": "https://upload.wikimedia.org/wikipedia/commons/thumb/4/41/Warner_TV_Italy.svg/1200px-Warner_TV_Italy.svg.png",
    "fox": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/fox-it.png",
    "nat geo wild": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/national-geographic-wild-it.png",
    "animal planet": "https://upload.wikimedia.org/wikipedia/commons/thumb/2/20/2018_Animal_Planet_logo.svg/2560px-2018_Animal_Planet_logo.svg.png",
    "boing": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/boing-it.png",
    "k2": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/k2-it.png",
    "discovery k2": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/k2-it.png",
    "nick jr": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/nick-jr-it.png",
    "nickelodeon": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/nickelodeon-it.png",
    "premium crime": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/premium-crime-it.png",
    "rakuten action movies": "https://img.utdstc.com/icon/7f6/a4a/7f6a4a47aa35e90d889cb8e71ed9a6930fe5832219371761736e87e880f85a5f:200",
    "rakuten comedy movies": "https://img.utdstc.com/icon/7f6/a4a/7f6a4a47aa35e90d889cb8e71ed9a6930fe5832219371761736e87e880f85a5f:200",
    "rakuten drama": "https://img.utdstc.com/icon/7f6/a4a/7f6a4a47aa35e90d889cb8e71ed9a6930fe5832219371761736e87e880f85a5f:200",
    "rakuten family": "https://img.utdstc.com/icon/7f6/a4a/7f6a4a47aa35e90d889cb8e71ed9a6930fe5832219371761736e87e880f85a5f:200",
    "rakuten top free": "https://img.utdstc.com/icon/7f6/a4a/7f6a4a47aa35e90d889cb8e71ed9a6930fe5832219371761736e87e880f85a5f:200",
    "rakuten tv shows": "https://img.utdstc.com/icon/7f6/a4a/7f6a4a47aa35e90d889cb8e71ed9a6930fe5832219371761736e87e880f85a5f:200",
    "boing plus": "https://upload.wikimedia.org/wikipedia/commons/thumb/7/79/Boing_Plus_logo_2020.svg/1200px-Boing_Plus_logo_2020.svg.png",
    "wwe channel": "https://upload.wikimedia.org/wikipedia/en/8/8c/WWE_Network_logo.jpeg",
    "rsi la 2": "https://upload.wikimedia.org/wikipedia/commons/thumb/f/f4/RSI_La_2_2012.svg/1200px-RSI_La_2_2012.svg.png",
    "rsi la 1": "https://upload.wikimedia.org/wikipedia/commons/thumb/b/be/RSI_La_1_2012.svg/1200px-RSI_La_1_2012.svg.png",
    "cartoon network": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/cartoon-network-it.png",
    "sky tg 24": "https://play-lh.googleusercontent.com/0RJjBW8_r64dWLAbG7kUVrkESbBr9Ukx30pDI83e5_o1obv2MTC7KSpBAIhhXvJAkXE",
    "tg com 24": "https://yt3.googleusercontent.com/ytc/AIdro_kVh4SupZFtHrALXp9dRWD9aahJOUfl8rhSF8VroefSLg=s900-c-k-c0x00ffffff-no-rj",
    "cartoonito": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/cartoonito-it.png",
    "super!": "https://upload.wikimedia.org/wikipedia/commons/thumb/2/2d/Super%21_logo_2021.svg/1024px-Super%21_logo_2021.svg.png",
    "deejay tv": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/deejay-tv-it.png",
    "cartoonito (backup)": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/cartoonito-it.png",
    "frisbee": "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/italy/frisbee-it.png",
    "catfish": "https://upload.wikimedia.org/wikipedia/commons/4/46/Catfish%2C_the_TV_Show_Logo.PNG",
    "disney+ film": "https://upload.wikimedia.org/wikipedia/commons/thumb/3/3e/Disney%2B_logo.svg/2560px-Disney%2B_logo.svg.png",
    "comedy central": "https://yt3.googleusercontent.com/FPzu1EWCI54fIh2j9JEp0NOzwoeugjL4sZTQCdoxoQY1U4QHyKx2L3wPSw27IueuZGchIxtKfv8=s900-c-k-c0x00ffffff-no-rj"
}

def clean_channel_name(name):
    """Pulisce e modifica il nome del canale aggiungendo (V)."""
    name = re.sub(r"\s*(\|E|\|H|\(6\)|\(7\)|\.c|\.s)\s*", "", name)
    return f"{name} (V)"

def normalize_tvg_id(name):
    """Normalizza il tvg-id con solo la prima lettera maiuscola."""
    return " ".join(word.capitalize() for word in name.replace("(V)", "").strip().split())

def assign_category(name):
    """Assegna la categoria in base ai due dizionari."""
    name_lower = name.lower()
    category1 = next((category for category, keywords in CATEGORY_KEYWORDS.items() if any(keyword in name_lower for keyword in keywords)), "")
    category2 = next((category for category, keywords in CATEGORY_KEYWORDS2.items() if any(keyword in name_lower for keyword in keywords)), "")
    categories = ";".join(filter(None, [category1, category2]))
    return categories if categories else "Altro"

def get_channel_list(signature, group="Italy"):
    headers = {
        "Accept-Encoding": "gzip",
        "User-Agent": "MediaHubMX/2",
        "Accept": "application/json",
        "Content-Type": "application/json; charset=utf-8",
        "mediahubmx-signature": signature
    }

    cursor = 0
    all_items = []

    while True:
        data = {
            "language": "de",
            "region": "AT",
            "catalogId": "vto-iptv",
            "id": "vto-iptv",
            "adult": False,
            "search": "",
            "sort": "name",
            "filter": {"group": group},
            "cursor": cursor,
            "clientVersion": "3.0.2"
        }

        try:
            response = requests.post("https://vavoo.to/vto-cluster/mediahubmx-catalog.json", json=data, headers=headers)
            response.raise_for_status()
            result = response.json()

            items = result.get("items", [])
            if not items:
                break  # Se non ci sono più canali, esce dal ciclo

            all_items.extend(items)
            cursor += len(items)  # Aggiorna il cursore con il numero di canali ricevuti

        except Exception as e:
            print(f"Errore durante il recupero della lista dei canali: {e}")
            break

    return {"items": all_items}

def generate_m3u(channels_json, signature, filename="channels.m3u8"):
    setup_logging()
    items = channels_json.get("items", [])
    if not items:
        print("Nessun canale disponibile.")
        return

    print(f"Generating M3U8 file with {len(items)} channels...")
    
    # Dizionario per tenere traccia dei nomi visti e del conteggio
    seen_names = {}

    with open(filename, "w", encoding="utf-8") as f:
        f.write('#EXTM3U url-tvg="http://epg-guide.com/it.gz"\n\n')

        for idx, item in enumerate(items, 1):
            original_name = item.get("name", "Unknown")
            
            # Controlla se il canale è nella lista da rimuovere
            if any(remove_word.lower() in original_name.lower() for remove_word in CHANNEL_REMOVE):
                print(f"Skipping channel {original_name} (in CHANNEL_REMOVE)")
                continue

            # Controlla se il canale è nella lista dei filtri da includere
            if not any(filter_word.lower() in original_name.lower() for filter_word in CHANNEL_FILTERS):
                logging.info(f"Excluded channel: {original_name}")
                continue

            # Pulisci il nome del canale e aggiungi (V)
            clean_name = clean_channel_name(original_name)
            
            # Aggiungi un contatore se abbiamo già visto questo nome
            count = seen_names.get(clean_name, 0) + 1
            seen_names[clean_name] = count
            if count > 1:
                display_name = f"{clean_name} ({count})"
            else:
                display_name = clean_name
            
            # Normalizza il tvg-id
            tvg_id = normalize_tvg_id(clean_name)
            tvg_id_clean = re.sub(r"\s*\(\d+\)$", "", tvg_id)  # Rimuove numeri tra parentesi solo per tvg-id
            
            # Ottieni l'URL originale
            original_link = item.get("url")
            if not original_link:
                continue

            print(f"Processing channel {idx}/{len(items)}: {display_name}")
            
            # Assegna le categorie
            category = assign_category(clean_name)
            
            # Cerca il logo
            base_tvg_id = tvg_id.lower()
            logo_url = CHANNEL_LOGOS.get(base_tvg_id, "")
            
            # Scrivi le informazioni nel file M3U8
            f.write(f'#EXTINF:-1 tvg-id="{tvg_id_clean}" tvg-name="{tvg_id}" tvg-logo="{logo_url}" group-title="{category}",{display_name}\n')
            f.write('#EXTVLCOPT:http-user-agent=MediaHubMX/2\n')
            f.write(f'{original_link}\n\n')

    print(f"M3U8 file generated successfully: {filename}")

def main():
    print("Getting authentication signature...")
    signature = get_auth_signature()
    if not signature:
        print("Failed to get authentication signature.")
        sys.exit(1)

    print("Getting channel list...")
    channels_json = get_channel_list(signature)
    if not channels_json:
        print("Failed to get channel list.")
        sys.exit(1)

    print("Generating M3U8 file...")
    generate_m3u(channels_json, signature)
    print("Done!")

if __name__ == "__main__":
    main()