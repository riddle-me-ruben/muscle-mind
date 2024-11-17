from flask import render_template, request, session, redirect, url_for, flash

"""
Description:
The QuizRetrievalManager class manages the retrieval and organization of quiz data. It allows fetching quiz details 
by ID, retrieving a user's quizzes, and building structured quiz data for rendering or processing. Additionally, 
it supports deleting quizzes and validating user email existence.

Semi-formal Notation:
/*@ requires db_manager != null (valid DatabaseManager instance) &&
@ analytics_manager != null or analytics_manager == None (depending on usage);
@ ensures Provides functionality to:
@   - Retrieve quiz data by ID;
@   - Retrieve a user's quizzes;
@   - Build and structure quiz data for rendering or further processing;
@   - Validate user emails in the database;
@*/
"""
class QuizRetrievalManager:
    
    """
    Description:
    Initializes the QuizRetrievalManager with a DatabaseManager for executing SQL queries and an optional 
    AnalyticsManager for user analytics.

    Semi-formal Notation:
    /*@ requires db_manager != null (valid DatabaseManager instance) &&
    @ analytics_manager == None || analytics_manager != null;
    @ ensures self.db_manager == db_manager &&
    @ ensures self.analytics_manager == analytics_manager;
    @*/
    """
    def __init__(self, db_manager, analytics_manager):
        self.db_manager = db_manager
        self.analytics_manager = analytics_manager

    """
    Description:
    Deletes a quiz from the database by its ID. It first nullifies related statistics in the `user_quiz_stats` table 
    and then removes the quiz record from the `quizzes` table.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID) &&
    @ user_email is a valid, existing string;
    @ ensures All rows in `user_quiz_stats` with quiz_id == quiz_id have quiz_id set to NULL;
    @ ensures The row in `quizzes` with quiz_id == quiz_id and user_email == user_email is deleted;
    @*/
    """
    def delete_quiz(self, quiz_id, user_email):       
        nullify_stats_query = "UPDATE user_quiz_stats SET quiz_id = NULL WHERE quiz_id = %s"
        self.db_manager.execute_commit(nullify_stats_query, (quiz_id,))
        # Delete the quiz itself
        delete_quiz_query = "DELETE FROM quizzes WHERE quiz_id = %s AND user_email = %s"
        self.db_manager.execute_commit(delete_quiz_query, (quiz_id, user_email))

    """
    Description:
    Fetches detailed data for a quiz by its ID, including metadata (title, audio file, play counts) and structured 
    questions with options and correct answers.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID);
    @ ensures If quiz exists:
    @   \result == {
    @     'title': string,
    @     'audio_file': string,
    @     'creator_play_count': int,
    @     'user_play_count': int,
    @     'creator_email': string,
    @     'questions': list of dictionaries containing question text, options, and correct answers
    @   };
    @ ensures If quiz does not exist: \result == None;
    @*/
    """
    def get_quiz_by_id(self, quiz_id):
        quiz = self.fetch_quiz(quiz_id)
        if not quiz:
            return None

        # Map the database fields to a dictionary
        fields = [
            'title', 'audio_file', 'creator_play_count', 'user_play_count', 'user_email'
        ]
        # Add dynamic fields for questions and options
        for i in range(1, 11):  # Max 10 questions
            fields.extend([
                f'question{i}', f'option{i}_1', f'option{i}_2',
                f'option{i}_3', f'option{i}_4', f'correct_option{i}'
            ])

        quiz_data = {fields[i]: quiz[0][i] for i in range(len(fields))}
        questions = self.build_questions(quiz_data)
        
        return {
            'title': quiz_data['title'],
            'audio_file': quiz_data['audio_file'],
            'creator_play_count': quiz_data['creator_play_count'],
            'user_play_count': quiz_data['user_play_count'],
            'creator_email': quiz_data['user_email'],
            'questions': questions
        }

    """
    Description:
    Fetches raw quiz data by its ID using a dynamically built SQL query.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID);
    @ ensures \result == Row of quiz data with metadata and questions if quiz_id exists;
    @ ensures If quiz_id does not exist: \result == [];
    @*/
    """
    def fetch_quiz(self, quiz_id):
        quiz_query, params = self.build_quiz_query(quiz_id)
        quiz = self.db_manager.execute_query(quiz_query, params)
        return quiz

    """
    Description:
    Constructs a dynamic SQL query to fetch quiz details, including metadata and up to 10 questions with their 
    respective options and correct answers.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID);
    @ ensures \result == (query_string, (quiz_id,)) &&
    @ query_string retrieves title, audio_file, play counts, creator email, and up to 10 questions with their options;
    @*/
    """
    def build_quiz_query(self, quiz_id):
        columns = ['title', 'audio_file', 'creator_play_count', 'user_play_count', 'user_email']
        num_questions = 10

        for i in range(num_questions):
            question_idx = i + 1
            columns.extend([
                f'question{question_idx}', f'option{question_idx}_1', f'option{question_idx}_2',
                f'option{question_idx}_3', f'option{question_idx}_4', f'correct_option{question_idx}'
            ])

        query = f"SELECT {', '.join(columns)} FROM quizzes WHERE quiz_id = %s"
        return query, (quiz_id,)

    """
    Description:
    Builds a list of questions with their options and correct answers from raw quiz data.

    Semi-formal Notation:
    /*@ requires quiz_data contains keys:
    @   f'question{i}', f'option{i}_1', ..., f'option{i}_4', f'correct_option{i}' for i in [1, 10];
    @ ensures \result == [
    @   {'question': string, 'options': [string, string, string, string], 'correct_option': string}
    @   for each valid question in quiz_data
    @ ];
    @*/
    """
    def build_questions(self, quiz_data):
        """Build the list of questions from the quiz data."""
        num_questions = 10
        questions = []

        for i in range(1, num_questions + 1):
            question_key = f'question{i}'
            if quiz_data.get(question_key):
                questions.append({
                    'question': quiz_data[question_key],
                    'options': [
                        quiz_data.get(f'option{i}_1'),
                        quiz_data.get(f'option{i}_2'),
                        quiz_data.get(f'option{i}_3'),
                        quiz_data.get(f'option{i}_4')
                    ],
                    'correct_option': quiz_data.get(f'correct_option{i}')
                })
        return questions

    """
    Description:
    Fetches quiz details by ID and renders the quiz detail page with the retrieved data. If the quiz does not exist, 
    returns a 404 error.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID) &&
    @ templates/quiz-detail.html exists;
    @ ensures If quiz exists:
    @   Renders 'quiz-detail.html' with quiz data and audio_file;
    @ ensures If quiz does not exist:
    @   \result == ("Quiz not found", 404);
    @*/
    """
    def quiz_detail(self, quiz_id):
        quiz = self.get_quiz_by_id(quiz_id)
        if not quiz:
            return "Quiz not found", 404
        audio_file = f"/static/media/{quiz.get('audio_file', 'option1.mp3')}"

        return render_template('quiz-detail.html', quiz=quiz, audio_file=audio_file)

    """
    Description:
    Retrieves all quizzes created by a specific user, returning basic metadata for each quiz.

    Semi-formal Notation:
    /*@ requires user_email is a valid string;
    @ ensures \result == [
    @   {'quiz_id': int, 'title': string, 'audio_file': string,
    @    'creator_play_count': int, 'user_play_count': int}
    @   for each quiz created by user_email
    @ ];
    @*/
    """
    def get_user_quizzes(self, user_email):
        query = "SELECT quiz_id, title, audio_file, creator_play_count, user_play_count FROM quizzes WHERE user_email = %s"
        result = self.db_manager.execute_query(query, (user_email,))
        
        quizzes = [{'quiz_id': row[0], 'title': row[1], 'audio_file': row[2], 'creator_play_count': row[3], 'user_play_count': row[4]} for row in result]
        return quizzes

    """
    Description:
    Fetches quizzes created by another user (specified via form or session) and renders the home page with these quizzes 
    and analytics data. If the email does not exist, displays an error message.

    Semi-formal Notation:
    /*@ requires session['email'] != null &&
    @ other_user_email is either session['other_user_email'] or request.form['other_user_email'];
    @ ensures If other_user_email exists in the database:
    @   Renders 'home.html' with quizzes and analytics for other_user_email;
    @ ensures If other_user_email does not exist:
    @   Displays a flash error message and redirects to home;
    @*/
    """
    def view_other_user_quizzes(self):
        other_user_email = session.get('other_user_email', request.form.get('other_user_email'))

        # Check if the email exists
        if not self.email_exists(other_user_email):
            flash(f"The email '{other_user_email}' does not exist!", 'error')
            return redirect(url_for('home'))  # Redirect back to the current page without changes

        # If email exists, proceed to fetch quizzes
        session['other_user_email'] = other_user_email  # Maintain context for valid email
        quizzes = self.get_user_quizzes(other_user_email)
        analytics = self.analytics_manager.get_user_analytics()

        return render_template('home.html',quizzes=quizzes,analytics=analytics,other_user_email=other_user_email)

    """
    Description:
    Restores the context to the signed-in user's quizzes by clearing the "other user" context and fetching quizzes 
    and analytics data for the logged-in user.

    Semi-formal Notation:
    /*@ requires session['email'] != null;
    @ ensures session['other_user_email'] == null &&
    @ ensures Renders 'home.html' with quizzes and analytics for session['email'];
    @*/
    """
    def restore_user_quizzes(self):
        session.pop('other_user_email', None)  # Clear other user's context
        user_email = session['email']
        quizzes = self.get_user_quizzes(user_email)
        analytics = self.analytics_manager.get_user_analytics()
        return render_template('home.html', quizzes=quizzes, analytics=analytics)

    """
    Description:
    Checks whether a given email exists in the `users` table of the database.

    Semi-formal Notation:
    /*@ requires email is a valid string;
    @ ensures \result == True if email exists in the database;
    @ ensures \result == False if email does not exist;
    @*/
    """
    def email_exists(self, email):
        query = "SELECT 1 FROM users WHERE email = %s LIMIT 1"
        result = self.db_manager.execute_query(query, (email,))
        return len(result) > 0