#!/usr/bin/python3.3
# python 3
from __future__ import with_statement
import itertools
import wave
import os, shutil

def _trivial__enter__(self):
    return self
def _self_close__exit__(self, exc_type, exc_value, traceback):
    self.close()

wave.Wave_read.__exit__ = wave.Wave_write.__exit__ = _self_close__exit__
wave.Wave_read.__enter__ = wave.Wave_write.__enter__ = _trivial__enter__

# http://stackoverflow.com/questions/307305/play-a-sound-with-python
try:
    import winsound, sys

    def play_sound(filename):
        winsound.PlaySound(filename, winsound.SND_FILENAME)
except ImportError:
    from wave import open as waveOpen
    import ossaudiodev
    from ossaudiodev import open as ossOpen
    ossaudiodev.oss_audio_device.__exit__ = _self_close__exit__
    ossaudiodev.oss_audio_device.__enter__ = _trivial__enter__
    def play_sound(filename):
        with waveOpen(filename, 'rb') as s:
            (nc, sw, fr, nf, comptype, compname) = s.getparams()
            with ossOpen('/dev/dsp','w') as dsp:
                try:
                    from ossaudiodev import AFMT_S16_NE
                except ImportError:
                    if byteorder == "little":
                        AFMT_S16_NE = ossaudiodev.AFMT_S16_LE
                    else:
                        AFMT_S16_NE = ossaudiodev.AFMT_S16_BE
                dsp.setparameters(AFMT_S16_NE, nc, fr)
                data = s.readframes(nf)
                dsp.write(data)




def combine_wav_files(out_file, *files):
    with wave.open(out_file, 'wb') as out:
        with wave.open(files[0], 'rb') as first_in:
            (nchannels, sampwidth, framerate, nframes, comptype, compname) = first_in.getparams()
            out.setparams(first_in.getparams())
        for filename in files:
            with wave.open(filename, 'rb') as cur_in:
                if (cur_in.getnchannels() != nchannels or
                    cur_in.getsampwidth() != sampwidth or
                    cur_in.getframerate() != framerate or
                    cur_in.getcomptype() != comptype or
                    cur_in.getcompname() != compname):
                    raise Exception('Mismatched file parameters.')
                out.writeframes(cur_in.readframes(cur_in.getnframes()))

def interleave_wav_files(out_file, file1, file2):
    with wave.open(out_file, 'wb') as out:
        with wave.open(file1, 'rb') as in1:
            with wave.open(file2, 'rb') as in2:
                sample_width = in1.getsampwidth()
                null_bytes = bytes(0 for i in range(sample_width))
                out.setparams(in1.getparams())
                if in1.getnchannels() == 1 and in2.getnchannels() == 1:
                    out.setnchannels(2)
                else:
                    out.setframerate(2 * in1.getframerate())
                frames1 = itertools.chain(in1.readframes(in1.getnframes()), itertools.repeat(0))
                frames2 = itertools.chain(in2.readframes(in2.getnframes()), itertools.repeat(0))
                frames = []
                for i in range(max((in1.getnframes(), in2.getnframes()))):
                    frames.extend(itertools.islice(frames1, sample_width))
                    frames.extend(itertools.islice(frames2, sample_width))
                out.writeframes(bytes(frames))

def add_wav_files(out_file, file1, file2):
    with wave.open(out_file, 'wb') as out:
        with wave.open(file1, 'rb') as in1:
            with wave.open(file2, 'rb') as in2:
                sample_width = in1.getsampwidth()
                null_bytes = bytes(0 for i in range(sample_width))
                out.setparams(in1.getparams())
                frames1 = itertools.chain(in1.readframes(in1.getnframes()), itertools.repeat(0))
                frames2 = itertools.chain(in2.readframes(in2.getnframes()), itertools.repeat(0))
                frames = []
                for i in range(max((in1.getnframes(), in2.getnframes()))):
                    frames.extend(bytes(itertools.islice(frames1, sample_width)) + bytes(itertools.islice(frames2, sample_width)))
                out.writeframes(bytes(frames))

def make_silence_from(out_file, in_file):
    with wave.open(in_file, 'rb') as in1:
        sample_width = in1.getsampwidth()
        null_bytes = bytes(0 for i in range(sample_width))
        params = in1.getparams()
        frames = list(null_bytes) * in1.getnframes()
    with wave.open(out_file, 'wb') as out:
        out.setparams(params)
        out.writeframes(bytes(frames))

def drop_wav_frames(infile, drop_n, outfile=None):
    with wave.open(infile, 'rb') as f:
        params = f.getparams()
        frames = f.readframes(f.getnframes() - drop_n)
    if outfile is None: outfile = infile
    if os.path.normpath(os.path.realpath(outfile)) == os.path.normpath(os.path.realpath(infile)):
        shutil.move(infile, infile + '.orig')
    with wave.open(outfile, 'wb') as f:
        f.setparams(params)
        f.writeframes(frames)

def get_wav_frames(infile):
    with wave.open(infile, 'rb') as f:
        return f.getnframes()
