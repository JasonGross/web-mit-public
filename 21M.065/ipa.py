#!/usr/bin/python3.0
# python 3
from __future__ import with_statement
from urllib.parse import urlencode, urlsplit
from urllib.request import urlretrieve
from http.client import HTTPConnection
import itertools
import os, shutil
import re
from pickle import load, dump
from sound import play_sound, combine_wav_files, interleave_wav_files, drop_wav_frames, get_wav_frames
from html import ampersand_encode

KNOWN_SOUNDS_PATH = os.path.join(os.getcwd(), 'known_sounds.dic')
try:
    with open(KNOWN_SOUNDS_PATH, 'rb') as f:
        known_sounds = load(f)
except Exception:
    try:
        with open(KNOWN_SOUNDS_PATH + '.bak', 'rb') as f:
            known_sounds = load(f)
    except Exception:
        known_sounds = {}

def _update_known_sounds():
    if not os.path.exists(KNOWN_SOUNDS_PATH + '.bak') and \
       os.path.exists(KNOWN_SOUNDS_PATH):
        shutil.move(KNOWN_SOUNDS_PATH, KNOWN_SOUNDS_PATH + '.bak')
    with open(KNOWN_SOUNDS_PATH, 'wb') as f:
        dump(known_sounds, f)
    try:
        if os.path.exists(KNOWN_SOUNDS_PATH + '.bak'):
            os.remove(KNOWN_SOUNDS_PATH + '.bak')
    except (IOError, WindowsError):
        pass
    

def to_phoneme(sentences):
    return '<phoneme alphabet="ipa" ph="' + sentences.strip(' .').replace(' ', '') + '"/>'

def chunk_text_by_spaces(text, max_len):
    cur = ''
    for chunk in text.split(' '):
        while len(cur) > max_len:
            yield cur[:max_len]
            cur = cur[max_len:]
        if len(cur) + 1 + len(chunk) <= max_len: # split preferentially at spaces
            cur += ' ' + chunk
        elif len(cur) > 0:
            yield cur
            cur = ''
        else:
            cur = ' ' + chunk
    if cur: yield cur

_tts_conn = HTTPConnection("192.20.225.36")
def get_att_tts(txt, filename=None, voice='crystal', verbose=False, conn=_tts_conn, cache=True, correct=True):
    txt = txt.strip(' .')
    if cache and voice in known_sounds and txt in known_sounds[voice]:
        return known_sounds[voice][txt]
    headers = {"Content-type": "application/x-www-form-urlencoded",
               "Accept": "text/plain"}
    reg = re.compile('<A HREF="([^"]+)">here</A>', re.IGNORECASE)
    params = urlencode({
        'txt': txt,
        'voice': voice
        })
    #print(params)
    conn.request("POST", "/tts/cgi-bin/nph-nvdemo", params, headers)
    response = conn.getresponse()
    #print('Response:')
    #print((response.status, response.reason))
    #print('Data:')
    data = response.read()
    #print(data)
    match = reg.search(str(data))
    if match:
        urlpath = match.groups()[0]
        url = 'http://192.20.225.36' + urlpath
        if verbose: print(url)
        if filename is None:
            filename = os.path.join(os.getcwd(),
                                    os.path.split(urlpath)[-1])
        ret = urlretrieve(url, filename)
        if cache:
            if voice not in known_sounds: known_sounds[voice] = {}
            if correct:
                empty_file = get_att_tts(to_phoneme(''), voice=voice, verbose=False, conn=conn, cache=False, correct=False)
                drop_wav_frames(ret[0], max(get_wav_frames(empty_file) - 6000, 0))
            known_sounds[voice][txt] = ret[0]
            _update_known_sounds()
        #print(ret)
    else:
        raise Exception('Response %s (%s)\nData: %s\nText:%s' % (response.status, response.reason, data, txt))
    return ret[0]


def ipa_to_wav(ipa, filename=None, voice='crystal', verbose=True):
    max_len = 150
    use_len = max_len - 10 - len(to_phoneme(''))
    ipa = ampersand_encode(ipa.strip('. '))
    chunks = [to_phoneme(chunk)
              for chunk in chunk_text_by_spaces(ipa, use_len)]
    files = []
    for chunk in chunks:
        filename = get_att_tts(chunk, voice=voice, verbose=verbose)
        files.append(filename)
    combined_name = os.path.join(os.getcwd(), '%d_%s_combined.wav' % (hash(ipa), voice))
    if verbose: print('Combining to %s...' % os.path.split(combined_name)[-1])
    combine_wav_files(combined_name,
                      *files)
    return combined_name


def interleave_ipa(ipa1, ipa2, play=True, voice1='mike', voice2='rich'):
    ipa1_file = ipa_to_wav(ipa1, voice=voice1)
    ipa2_file = ipa_to_wav(ipa2, voice=voice2)
    interleaved_name = os.path.join(os.getcwd(), '%s_combined.wav' % hash(ipa1 + '\0' + ipa2))
    interleave_wav_files(interleaved_name,
                         ipa1_file,
                         ipa2_file)
    if play: play_sound(interleaved_name)
    return interleaved_name

def close_connection():
    _tts_conn.close()
