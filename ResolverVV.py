#!/usr/bin/env python3
# -*- coding: utf-8 -*-
#
# Vavoo Resolver per OMG TV
# Questo script risolve gli URL di streaming di Vavoo
# Testato il 27/2/2025
# Versione 1.0.6 - Ottimizzata risoluzione e proxy con nuovo flusso e log ridotto

import sys
import json
import os
import requests
import time
import re
import logging
from urllib.parse import urlparse, parse_qs, urlencode

# Configurazione
RESOLVER_VERSION = "1.0.4"
CACHE_DURATION = 20 * 60  # 30 minuti

# Configurazione del logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.FileHandler("vavoo_resolver.log"),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger("vavoo_resolver")

def create_proxy_session(proxy_config):
    """
    Crea una sessione configurata per utilizzare il proxy MediaFlow
    """
    if not proxy_config:
        logger.info("Utilizzo connessione diretta (nessun proxy)")
        return requests.Session()
    
    try:
        proxy_url = proxy_config.get('url', '').strip('/')
        proxy_pwd = proxy_config.get('password', '')
        
        if not proxy_url:
            logger.warning("URL proxy non specificato, utilizzo connessione diretta")
            return requests.Session()
        
        proxy_session = requests.Session()
        
        logger.info(f"Configurazione proxy: URL={proxy_url}")
        
        return proxy_session
        
    except Exception as e:
        logger.error(f"Errore nella configurazione del proxy: {e}")
        return requests.Session()

def build_proxy_url(proxy_config, original_url, headers=None):
    """
    Costruisce l'URL per il proxy con endpoint stream standard
    """
    if not proxy_config:
        return original_url
    
    proxy_url = proxy_config.get('url', '').strip('/')
    proxy_pwd = proxy_config.get('password', '')
    
    # Prepara i parametri per il proxy
    params = {
        'api_password': proxy_pwd,
        'd': original_url
    }
    
    # Aggiungi headers con prefisso h_
    if headers:
        headers_map = {
            'User-Agent': headers.get('User-Agent', headers.get('user-agent', '')),
            'Referer': headers.get('Referer', headers.get('referer', '')),
            'Origin': headers.get('Origin', headers.get('origin', ''))
        }
        
        for key, value in headers_map.items():
            if value:
                params[f'h_{key.lower()}'] = value
    
    # Costruisci l'URL completo del proxy usando sempre /proxy/stream
    proxy_full_url = f"{proxy_url}/proxy/stream?{urlencode(params)}"
    
    logger.info(f"URL proxy generato: {proxy_full_url}")
    
    return proxy_full_url

def get_auth_signature(session):
    """
    Ottiene la firma di autenticazione necessaria per le richieste API
    """
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
        "firstAppStart": int(time.time() * 1000) - 3600000,  # 1 ora fa
        "lastAppStart": int(time.time() * 1000) - 60000,     # 1 minuto fa
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
        logger.info("Richiesta firma di autenticazione...")
        response = session.post("https://www.vavoo.tv/api/app/ping", json=data, headers=headers)
        response.raise_for_status()
        res_json = response.json()
        signature = res_json.get("addonSig")
        if signature:
            logger.info("Firma di autenticazione ottenuta con successo")
            return signature
        else:
            logger.error("Firma non trovata nella risposta")
            return None
    except Exception as e:
        logger.error(f"Errore durante il recupero della firma: {e}")
        return None

def resolve_vavoo_url(url, headers=None, channel_name=None, session=None, signature=None):
    """
    Risolve un URL di Vavoo
    """
    if not url or "localhost" in url:
        return {"resolved_url": url, "headers": headers or {}}

    # Se non è stata fornita una sessione, usa requests standard
    if session is None:
        session = requests.Session()

    # Usa la firma passata come parametro, altrimenti ottienila
    if not signature:
        signature = get_auth_signature(session)
    
    if not signature:
        logger.error("Impossibile ottenere la firma di autenticazione")
        return {"resolved_url": url, "headers": headers or {}}

    # Prepara gli header per la richiesta
    request_headers = {
        "user-agent": "MediaHubMX/2",
        "accept": "application/json",
        "content-type": "application/json; charset=utf-8",
        "accept-encoding": "gzip",
        "mediahubmx-signature": signature
    }

    # Prepara i dati per la richiesta
    data = {
        "language": "de",
        "region": "AT",
        "url": url,
        "clientVersion": "3.0.2"
    }

    try:
        response = session.post(
            "https://vavoo.to/vto-cluster/mediahubmx-resolve.json", 
            json=data, 
            headers=request_headers
        )
        response.raise_for_status()
        result = response.json()
        
        if isinstance(result, list) and result and "url" in result[0]:
            resolved_url = result[0]["url"]
            logger.info(f"URL risolto con successo: {resolved_url[:50]}...")
            
            # Prepara gli header per lo streaming
            stream_headers = headers.copy() if headers else {}
            stream_headers.update({
                "User-Agent": "okhttp/4.11.0",
                "Origin": "https://vavoo.to",
                "Referer": "https://vavoo.to/"
            })
            
            return {
                "resolved_url": resolved_url,
                "headers": stream_headers
            }
        else:
            logger.error(f"Formato di risposta non valido: {result}")
            return {"resolved_url": url, "headers": headers or {}}
            
    except Exception as e:
        logger.error(f"Errore durante la risoluzione del link: {e}")
        return {"resolved_url": url, "headers": headers or {}}

def resolve_link(url, headers=None, channel_name=None, proxy_config=None):
    """
    Funzione principale che risolve un link
    Solo risolve gli URL che contengono vavoo.to, 
    per altri URL restituisce immediatamente l'URL originale
    """
    logger.info(f"Risoluzione URL: {url}")
    logger.info(f"Canale: {channel_name}")
    
    # Se l'URL non è di Vavoo
    if "vavoo.to" not in url:
        # Restituisci l'URL originale, con proxy se configurato
        if proxy_config:
            proxy_url = build_proxy_url(proxy_config, url, headers)
            return {
                "resolved_url": url,  # URL originale NON modificato
                "proxied_url": proxy_url,  # URL proxied generato
                "headers": headers or {}
            }
        # Se non c'è proxy, restituisci solo l'URL originale
        return {"resolved_url": url, "headers": headers or {}}
    
    # Per URL Vavoo, esegui la risoluzione completa
    session = create_proxy_session(proxy_config) if proxy_config else requests.Session()
    
    try:
        # Ottieni la firma di autenticazione una sola volta
        signature = get_auth_signature(session)
        if not signature:
            logger.error("Impossibile ottenere la firma di autenticazione")
            return {"resolved_url": url, "headers": headers or {}}
        
        # Risolvi l'URL Vavoo usando la sessione proxy e la firma già ottenuta
        resolved_result = resolve_vavoo_url(url, headers, channel_name, session, signature)
        
        # Se proxy è configurato, passa la risoluzione attraverso il proxy
        if proxy_config:
            proxy_url = build_proxy_url(proxy_config, resolved_result['resolved_url'], resolved_result['headers'])
            
            return {
                "resolved_url": resolved_result['resolved_url'],
                "proxied_url": proxy_url,
                "headers": resolved_result['headers']
            }
        
        return resolved_result
    
    except Exception as e:
        logger.error(f"Errore generale nella risoluzione: {e}")
        return {"resolved_url": url, "headers": headers or {}}

def main():
    """
    Funzione principale che gestisce i parametri di input
    """
    # Verifica parametri di input
    if len(sys.argv) < 2:
        print("Utilizzo: python3 vavoo_resolver.py [--check|--resolve input_file output_file]")
        sys.exit(1)
    
    # Comando check: verifica che lo script sia valido
    if sys.argv[1] == "--check":
        print("resolver_ready: True")
        sys.exit(0)
    
    # Comando resolve: risolvi un URL
    if sys.argv[1] == "--resolve" and len(sys.argv) >= 4:
        input_file = sys.argv[2]
        output_file = sys.argv[3]
        
        try:
            # Leggi i parametri di input
            with open(input_file, 'r') as f:
                input_data = json.load(f)
            
            url = input_data.get('url', '')
            headers = input_data.get('headers', {})
            channel_name = input_data.get('channel_name', 'unknown')
            proxy_config = input_data.get('proxy_config', None)
            
            # Risolvi l'URL
            result = resolve_link(url, headers, channel_name, proxy_config)
            
            # Scrivi il risultato
            with open(output_file, 'w') as f:
                json.dump(result, f, indent=2)
            
            print(f"URL risolto salvato in: {output_file}")
            sys.exit(0)
        except Exception as e:
            print(f"Errore: {str(e)}")
            sys.exit(1)
    
    print("Comando non valido")
    sys.exit(1)

if __name__ == "__main__":
    main()