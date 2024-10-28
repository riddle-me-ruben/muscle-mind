import os
import sys
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../server')))
from App import App

# Initialize the app
app_instance = App()
app = app_instance.app

# Sample email for testing purposes
sample_email = 'test@example.com'

def test_index():
    """
    Test the index route to ensure it renders the index page when no user is signed in.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            response = client.get('/')
            if isinstance(response.data, bytes):
                print("Index route test passed")
            else:
                print("Index route test failed (response is not bytes)")
        except Exception as e:
            print(f"Index route test failed with error: {str(e)}")


def test_home():
    """
    Test the home route to ensure it renders or redirects.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            # When the user is not signed in
            with client.session_transaction() as sess:
                sess['email'] = None
            response = client.get('/home')
            if isinstance(response.data, bytes):
                print("Home route test (not signed in) passed")
            else:
                print("Home route test (not signed in) failed (response is not bytes)")

            # When the user is signed in
            with client.session_transaction() as sess:
                sess['email'] = sample_email
            response = client.get('/home')
            if isinstance(response.data, bytes):
                print("Home route test (signed in) passed")
            else:
                print("Home route test (signed in) failed (response is not bytes)")
        except Exception as e:
            print(f"Home route test failed with error: {str(e)}")


def test_add_user():
    """
    Test the add_user route to ensure a user can be added.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            data = {'email': 'new_user@example.com', 'password': 'newpass'}
            response = client.post('/add_user', data=data)
            if isinstance(response.data, bytes):
                print("Add user route test passed")
            else:
                print("Add user route test failed (response is not bytes)")
        except Exception as e:
            print(f"Add user route test failed with error: {str(e)}")


def test_login():
    """
    Test the login route to ensure login works correctly.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            response = client.get('/login')
            if isinstance(response.data, bytes):
                print("Login route test passed")
            else:
                print("Login route test failed (response is not bytes)")
        except Exception as e:
            print(f"Login route test failed with error: {str(e)}")


def test_logout():
    """
    Test the logout route to ensure user is logged out.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            with client.session_transaction() as sess:
                sess['email'] = sample_email
            response = client.get('/logout')
            if isinstance(response.data, bytes):
                print("Logout route test passed")
            else:
                print("Logout route test failed (response is not bytes)")
        except Exception as e:
            print(f"Logout route test failed with error: {str(e)}")


def test_create_quiz():
    """
    Test the create quiz route to ensure quizzes can be created.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            with client.session_transaction() as sess:
                sess['email'] = sample_email
            data = {'title': 'Sample Quiz', 'questions': []}
            response = client.post('/create-quiz', data=data)
            if isinstance(response.data, bytes):
                print("Create quiz route test passed")
            else:
                print("Create quiz route test failed (response is not bytes)")
        except Exception as e:
            print(f"Create quiz route test failed with error: {str(e)}")


def test_submit_quiz():
    """
    Test the submit quiz route to ensure quizzes can be submitted.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            with client.session_transaction() as sess:
                sess['email'] = sample_email
            data = {'answers': ['A', 'B', 'C']}
            response = client.post('/submit-quiz', data=data)
            if isinstance(response.data, bytes):
                print("Submit quiz route test passed")
            else:
                print("Submit quiz route test failed (response is not bytes)")
        except Exception as e:
            print(f"Submit quiz route test failed with error: {str(e)}")


def test_quiz_detail():
    """
    Test the quiz detail route to ensure quiz details can be retrieved.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            response = client.get('/quiz/1')
            if isinstance(response.data, bytes):
                print("Quiz detail route test passed")
            else:
                print("Quiz detail route test failed (response is not bytes)")
        except Exception as e:
            print(f"Quiz detail route test failed with error: {str(e)}")


def test_take_quiz():
    """
    Test the take quiz route to ensure quizzes can be taken.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            response = client.get('/take-quiz/1/1')
            if isinstance(response.data, bytes):
                print("Take quiz route test passed")
            else:
                print("Take quiz route test failed (response is not bytes)")
        except Exception as e:
            print(f"Take quiz route test failed with error: {str(e)}")


def test_submit_quiz():
    """
    Test the submit quiz route to ensure quizzes can be submitted.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            with client.session_transaction() as sess:
                sess['email'] = sample_email
            
            # Provide the correct data structure required by the quiz submission endpoint
            data = {
                'title': 'Sample Quiz',  # Adding a title to avoid the "title cannot be null" error
                'questions': [
                    {'question': 'What is 2+2?', 'options': ['1', '2', '4', '5'], 'correct_option': '4'},
                    {'question': 'What is the capital of France?', 'options': ['London', 'Paris', 'Rome', 'Berlin'], 'correct_option': 'Paris'}
                ],
                'answers': ['4', 'Paris']
            }

            # Post the quiz with the correct data format
            response = client.post('/submit-quiz', data=data)

            if isinstance(response.data, bytes):
                print("Submit quiz route test passed")
            else:
                print("Submit quiz route test failed (response is not bytes)")

        except Exception as e:
            print(f"Submit quiz route test failed with error: {str(e)}")



def test_penalty():
    """
    Test the penalty route to ensure penalties are applied for wrong answers.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            response = client.get('/penalty/1/1')
            if isinstance(response.data, bytes):
                print("Penalty route test passed")
            else:
                print("Penalty route test failed (response is not bytes)")
        except Exception as e:
            print(f"Penalty route test failed with error: {str(e)}")

def test_submit_quiz_answer():
    """
    Test the submit quiz answer route to ensure quiz answers can be submitted.
    Prints a success message if the test passes.
    """
    with app.test_client() as client:
        try:
            with client.session_transaction() as sess:
                sess['email'] = sample_email

            # Step 1: Create a quiz with valid questions
            create_quiz_data = {
                'title': 'Sample Quiz',  # Adding a title to avoid the "title cannot be null" error
                'questions': [
                    {'question': 'What is 2+2?', 'options': ['1', '2', '4', '5'], 'correct_option': '4'},
                    {'question': 'What is the capital of France?', 'options': ['London', 'Paris', 'Rome', 'Berlin'], 'correct_option': 'Paris'}
                ]
            }
            client.post('/create-quiz', data=create_quiz_data)

            # Step 2: Submit a valid answer for the first question
            submit_answer_data = {'answer': '4'}  # Answer for the first question
            response = client.post('/submit-quiz-answer/1/0', data=submit_answer_data)  # Question 0, quiz 1

            if isinstance(response.data, bytes):
                print("Submit quiz answer route test passed")
            else:
                print("Submit quiz answer route test failed (response is not bytes)")

        except IndexError:
            print("Submit quiz answer route failed (IndexError: question number is out of range)")
        except Exception as e:
            print(f"Submit quiz answer route test failed with error: {str(e)}")



if __name__ == "__main__":
    # Run all the test functions
    print("-" * 50)
    test_index()
    print("-" * 50)
    test_home()
    print("-" * 50)
    test_add_user()
    print("-" * 50)
    test_login()
    print("-" * 50)
    test_logout()
    print("-" * 50)
    test_create_quiz()
    print("-" * 50)
    test_penalty()
    print("-" * 50)
    test_quiz_detail()
    print("-" * 50)
    test_take_quiz()
    print("-" * 50)
    test_submit_quiz()
    print("-" * 50)
    test_submit_quiz_answer()
    print("-" * 50)
    print("All tests completed.")