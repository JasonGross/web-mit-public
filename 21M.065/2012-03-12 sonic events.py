#!/usr/bin/python3.3
# python 3
import os
import tempfile
from sound import add_wav_files, combine_wav_files, play_sound, \
     get_wav_frames, make_silence_from, drop_wav_frames, interleave_wav_files
from util import lcm

clap_pattern_generator_1 = [1,1,1,0,1,0,1,1,0]
clap_pattern_generator_2 = [1,1,1,0,1,0,1,1,0] * 2

def make_clap_pattern(generator, n_times, space_count=1):
    gen_list = list(generator)
    for i in range(n_times):
        for j in gen_list:
            yield j
        for j in range(space_count):
            yield 0

def make_claps(pattern, clap_file, out_file, offset=0):
    initial_silence_file_obj = tempfile.NamedTemporaryFile(suffix='.wav')
    clap_silence_file_obj = tempfile.NamedTemporaryFile(suffix='.wav')
    
    initial_silence_file = initial_silence_file_obj.name
    clap_silence_file = clap_silence_file_obj.name
    
    initial_silence_file_obj.close()
    clap_silence_file_obj.close()
    
    make_silence_from(clap_silence_file, clap_file)
    nframes = get_wav_frames(clap_silence_file)
    drop_wav_frames(clap_silence_file, int(nframes * (1 - offset)), outfile=initial_silence_file)
    
    combine_wav_files(out_file, initial_silence_file,
                      *[(clap_file if pat else clap_silence_file) for pat in pattern])
    os.remove(initial_silence_file)
    os.remove(clap_silence_file)

def make_clapping_music():
    clap_pattern_generator_1 = [1,1,1,0,1,1,0,1,0,1,1,0] * 4

    l1 = list(make_clap_pattern(clap_pattern_generator_1, 1, space_count=0))
    l2 = list(make_clap_pattern(clap_pattern_generator_1, 1, space_count=1))

    os.chdir(r"D:\Documents\Dropbox\MIT\2011-2012\21M.065 - Intro to Musical Composition")
    make_claps(l1, "single_clap.wav",
               "clap_pattern_1.wav",
               offset=0)
    make_claps(l2, "single_clap.wav",
               "clap_pattern_2.wav",
               offset=0.2)

    print('adding')

    interleave_wav_files("clapping_music.wav", "clap_pattern_1.wav", "clap_pattern_2.wav")


make_clapping_music()
input('done')
    
              


    

clap_pattern_generator_1 = [1,0,1,1,0,1,1,1,0]
clap_pattern_generator_1 = [1,1,1,1,0,1,1,1,0]
clap_pattern_generator_1 = [1,0,1,1,0,1,1,1,0]
clap_pattern_generator_1 = [1,1,0,1,0,1,1,0]
clap_pattern_generator_1 = [1,0,1,1,0,1,1,1,0]
clap_pattern_generator_2 = clap_pattern_generator_1 * 2
clap_pattern_generator_3 = clap_pattern_generator_1 * 3

total = lcm(len(clap_pattern_generator_1),
            len(clap_pattern_generator_2),
            len(clap_pattern_generator_3)) * len(clap_pattern_generator_1) // 2

total = int(90 / 0.25)
l1 = list(make_clap_pattern(clap_pattern_generator_1, total // (len(clap_pattern_generator_1)), space_count=0))
l2 = list(make_clap_pattern(clap_pattern_generator_2, total // (1 + len(clap_pattern_generator_2)), space_count=1))
l3 = list(make_clap_pattern(clap_pattern_generator_3, total // (1 + len(clap_pattern_generator_3)), space_count=1))
os.chdir(r"D:\Documents\Dropbox\MIT\2011-2012\21M.065 - Intro to Musical Composition")
make_claps(l1, "single_clap.wav",
           "clap_pattern_1.wav",
           offset=0)
make_claps(l2, "440_tone.wav",
           "clap_pattern_2.wav",
           offset=0.1)
make_claps(l3, "dtmf_tone.wav",
           "clap_pattern_3.wav",
           offset=0.2)
print('adding')
#add_wav_files
interleave_wav_files("clap_pattern_12.wav", "clap_pattern_1.wav", "clap_pattern_2.wav")
