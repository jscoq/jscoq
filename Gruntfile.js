module.exports = function (grunt) {
    // grunt.loadNpmTasks('grunt-wiredep');
    grunt.loadNpmTasks('grunt-bower-concat');
    grunt.initConfig({
        // wiredep: {
        //     target: {
        //         src: 'panelside.html'
        //     }
        // },
        
        bower_concat: {
            all: {
                dest: {
                    'js': 'js/_bower.js',
                    'css': 'css/_bower.css'
                },
            }
        }
    });
    grunt.registerTask('default', ['bower_concat']);
};